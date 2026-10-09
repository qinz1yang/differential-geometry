import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitSphere
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationEngine

/-!
# The incidence cycle rank and the single-sphere step of the relative normalisation

Lane BR, tier R2 (design `handoffs/20261004-design-br-relative-normalisation.md` §0.3, §3.4.5;
review 20 §1.3). A finite multigraph is a map `ends : I → Sym2 V` (loops and parallel edges
allowed); `cycleRank V I = |I| + 1 − |V|`. When the graph is connected, `|V| ≤ |I| + 1`
and `cycleRank V I + |V| = |I| + 1` (`cycleRank_add_card`), so the subtraction is honest. Two
parallel non-separating spheres of `S² × S¹` (two vertices, two parallel edges) have cycle rank
`1` (`cycleRank_parallel_two`): the correction counts the actual capped components, not the
spheres that look non-separating one at a time.

For a spherical cut-cap transition `X` the incidence graph has the actual capped components as
vertices (retained and discarded alike), the tubes as edges, and ends `X.cutCapVertex a false`,
`X.cutCapVertex a true` (`cutCapEnds`). For one tube it is connected
(`cutCapGraph_connected_of_subsingleton`, from `eq_cutCapVertex_of_subsingleton`), with cycle rank
`0` when the two sides lie in different components and `1` otherwise
(`cutCapCycleRank_of_ne`, `cutCapCycleRank_of_eq`). `exists_singleTubeExpansion` turns an oriented
form of the single-sphere dichotomy (`M ≅⁺ A # B`, resp. `M ≅⁺ A # S`) and stages realising the
capped components into an engine expansion indexed by ALL capped components, with exactly
`cutCapCycleRank X` extra summands `S`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology

universe u v w

namespace GC.Seifert.RelativeNormalization

local macro "OIso " A:term:max ppSpace B:term:max : term =>
  `(Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
    (ConnectedClosedOrientedManifold.toClosedOrientedManifold $A)
    (ConnectedClosedOrientedManifold.toClosedOrientedManifold $B)))

def incidenceGraph {V : Type v} {I : Type w} (ends : I → Sym2 V) : _root_.SimpleGraph V :=
  _root_.SimpleGraph.fromRel fun a b => ∃ i, ends i = s(a, b)

def cycleRank (V : Type v) (I : Type w) : ℕ := Nat.card I + 1 - Nat.card V

theorem card_le_card_add_one {V : Type v} {I : Type w} [Finite I] (ends : I → Sym2 V)
    (hconn : (incidenceGraph ends).Connected) : Nat.card V ≤ Nat.card I + 1 := by
  have := Fintype.ofFinite I
  obtain ⟨b, hb⟩ :=
    DifferentialGeometry.Topology.SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends ends hconn
  rw [Nat.card_eq_fintype_card (α := I)]
  omega

theorem cycleRank_add_card {V : Type v} {I : Type w} [Finite I] (ends : I → Sym2 V)
    (hconn : (incidenceGraph ends).Connected) :
    cycleRank V I + Nat.card V = Nat.card I + 1 := by
  have := card_le_card_add_one ends hconn
  rw [cycleRank]
  omega

theorem eq_cycleRank_of_add_card {V : Type v} {I : Type w} [Finite I] (ends : I → Sym2 V)
    (hconn : (incidenceGraph ends).Connected) {b : ℕ} (hb : b + Nat.card V = Nat.card I + 1) :
    b = cycleRank V I := by
  have := cycleRank_add_card ends hconn
  omega

theorem cycleRank_parallel_two : cycleRank (Fin 2) (Fin 2) = 1 := by
  simp [cycleRank]

theorem cycleRank_loop : cycleRank PUnit.{v + 1} PUnit.{w + 1} = 1 := by
  simp [cycleRank]

theorem cycleRank_bridge : cycleRank (Fin 2) PUnit.{w + 1} = 0 := by
  simp [cycleRank]

theorem incidenceGraph_parallel_two_connected :
    (incidenceGraph fun _ : Fin 2 => s((0 : Fin 2), 1)).Connected := by
  have hadj : (incidenceGraph fun _ : Fin 2 => s((0 : Fin 2), 1)).Adj 0 1 := by
    rw [incidenceGraph, _root_.SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨0, rfl⟩⟩
  refine ⟨fun a b => ?_⟩
  have key : ∀ c : Fin 2, (incidenceGraph fun _ : Fin 2 => s((0 : Fin 2), 1)).Reachable 0 c := by
    intro c
    fin_cases c
    · exact _root_.SimpleGraph.Reachable.refl _
    · exact hadj.reachable
  exact (key a).symm.trans (key b)

section Transition

variable {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
  (X : SphericalCutCapTransition M.toClosedOrientedManifold Q)

def cutCapEnds (a : X.tubes.Index) : Sym2 (ConnectedComponents X.capped.Carrier) :=
  s(X.cutCapVertex a false, X.cutCapVertex a true)

def cutCapCycleRank : ℕ := cycleRank (ConnectedComponents X.capped.Carrier) X.tubes.Index

theorem cutCapGraph_connected_of_subsingleton [Subsingleton X.tubes.Index] (a : X.tubes.Index) :
    (incidenceGraph (cutCapEnds X)).Connected := by
  have hr : ∀ K, (incidenceGraph (cutCapEnds X)).Reachable (X.cutCapVertex a false) K := by
    intro K
    rcases GC.Endpoint.eq_cutCapVertex_of_subsingleton X a K with rfl | rfl
    · exact _root_.SimpleGraph.Reachable.refl _
    · by_cases h : X.cutCapVertex a false = X.cutCapVertex a true
      · rw [h]
      · refine _root_.SimpleGraph.Adj.reachable ?_
        rw [incidenceGraph, _root_.SimpleGraph.fromRel_adj]
        exact ⟨h, Or.inl ⟨a, rfl⟩⟩
  have : Nonempty (ConnectedComponents X.capped.Carrier) := ⟨X.cutCapVertex a false⟩
  exact ⟨fun K L => (hr K).symm.trans (hr L)⟩

private theorem card_index_eq_one [Subsingleton X.tubes.Index] (a : X.tubes.Index) :
    Nat.card X.tubes.Index = 1 := by
  have : Unique X.tubes.Index := uniqueOfSubsingleton a
  exact Nat.card_unique

theorem cutCapCycleRank_of_ne [Subsingleton X.tubes.Index] (a : X.tubes.Index)
    (h : X.cutCapVertex a false ≠ X.cutCapVertex a true) : cutCapCycleRank X = 0 := by
  have hV : Nat.card (ConnectedComponents X.capped.Carrier) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨X.cutCapVertex a false, X.cutCapVertex a true, h, ?_⟩
    ext K
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact GC.Endpoint.eq_cutCapVertex_of_subsingleton X a K
  rw [cutCapCycleRank, cycleRank, hV, card_index_eq_one X a]

theorem cutCapCycleRank_of_eq [Subsingleton X.tubes.Index] (a : X.tubes.Index)
    (h : X.cutCapVertex a false = X.cutCapVertex a true) : cutCapCycleRank X = 1 := by
  have hV : Nat.card (ConnectedComponents X.capped.Carrier) = 1 := by
    have : Unique (ConnectedComponents X.capped.Carrier) :=
      ⟨⟨X.cutCapVertex a false⟩, fun K => by
        rcases GC.Endpoint.eq_cutCapVertex_of_subsingleton X a K with rfl | rfl
        · rfl
        · exact h.symm⟩
    exact Nat.card_unique
  rw [cutCapCycleRank, cycleRank, hV, card_index_eq_one X a]

theorem exists_singleTubeExpansion {S : Type v}
    (carrier : S → ConnectedClosedOrientedManifold.{u} 3)
    (Y : ConnectedClosedOrientedManifold.{u} 3) (prot : S → Type u) (pred : ∀ s, prot s → Prop)
    (G : S → Prop) (s : S) [Subsingleton X.tubes.Index] (a : X.tubes.Index)
    (stageOf : ConnectedComponents X.capped.Carrier → S)
    (hcarrier : ∀ c, OIso (X.capped.component c) (carrier (stageOf c)))
    (hG : ∀ c, G (stageOf c))
    (hsep : X.cutCapVertex a false ≠ X.cutCapVertex a true →
      OIso (connectedSum (X.capped.component (X.cutCapVertex a false))
        (X.capped.component (X.cutCapVertex a true))) M)
    (hloop : X.cutCapVertex a false = X.cutCapVertex a true →
      OIso (connectedSum (X.capped.component (X.cutCapVertex a false)) Y) M)
    (hs : OIso M (carrier s))
    (seam : prot s ≃ Σ c, prot (stageOf c))
    (hseam : ∀ p, pred s p ↔ pred (stageOf (seam p).1) (seam p).2) :
    ∃ E : Expansion carrier Y prot pred G s, E.count = cutCapCycleRank X := by
  have tr : ∀ {A B C : ConnectedClosedOrientedManifold.{u} 3}, OIso A B → OIso B C → OIso A C :=
    fun h₁ h₂ => h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩
  have cs : ∀ {A A' B B' : ConnectedClosedOrientedManifold.{u} 3}, OIso A A' → OIso B B' →
      OIso (connectedSum A B) (connectedSum A' B') :=
    fun h₁ h₂ => h₁.elim fun f => h₂.elim fun g =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph f g
  have hc : ∀ c, OIso (carrier (stageOf c)) (X.capped.component c) :=
    fun c => (hcarrier c).elim fun f => ⟨f.symm⟩
  by_cases h : X.cutCapVertex a false = X.cutCapVertex a true
  · refine ⟨
      { Index := ConnectedComponents X.capped.Carrier
        stage := stageOf
        enum := [X.cutCapVertex a false]
        nodup := List.nodup_singleton _
        complete := fun K => ?_
        count := 1
        good := hG
        reconstruction := ?_
        seam := seam
        seam_pred := hseam }, (cutCapCycleRank_of_eq X a h).symm⟩
    · rcases GC.Endpoint.eq_cutCapVertex_of_subsingleton X a K with rfl | rfl
      · exact List.mem_singleton_self _
      · rw [← h]
        exact List.mem_singleton_self _
    · exact tr (tr (cs (hc _) ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩) (hloop h)) hs
  · refine ⟨
      { Index := ConnectedComponents X.capped.Carrier
        stage := stageOf
        enum := [X.cutCapVertex a false, X.cutCapVertex a true]
        nodup := List.nodup_cons.mpr ⟨by simpa using h, List.nodup_singleton _⟩
        complete := fun K => ?_
        count := 0
        good := hG
        reconstruction := ?_
        seam := seam
        seam_pred := hseam }, (cutCapCycleRank_of_ne X a h).symm⟩
    · rcases GC.Endpoint.eq_cutCapVertex_of_subsingleton X a K with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · exact tr (tr (cs (hc _) (hc _)) (hsep h)) hs

end Transition

end GC.Seifert.RelativeNormalization
