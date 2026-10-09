import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedCongruence
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws

/-!
# The descent engine of the relative normalisation

Lane BR, tier R1 (design `handoffs/20261004-design-br-relative-normalisation.md` §4). Stages of
any type `S` carry a closed connected oriented manifold `carrier s`, a measure `μ s : ℕ`, a type
`prot s` of protected seams and a predicate `pred s` on them. An `Expansion carrier X prot pred G s`
records a finite family of stages, indexed by an arbitrary type with a complete duplicate-free
enumeration (so equal factors are never merged), all satisfying `G`, a count `b` of extra summands
`X` (the `S² × S¹` correction), an oriented diffeomorphism from
`(#ᵢ carrier (stage i)) # (#^b X)` to `carrier s`, and an equivalence of the protected seams of `s`
with the disjoint union of those of the stages that preserves `pred`.

Expansions compose (`Expansion.bind`): indices form a sigma type, enumerations are flattened,
counts add, and the reconstruction uses `finiteConnectedSum_map_flatten` (a connected sum of
connected sums is the connected sum of the concatenation) and a permutation moving the extra
summands to the end (`perm_flatten_map_append_replicate`). A step oracle giving, for every
non-terminal stage, an expansion into stages of strictly smaller measure yields by strong induction
on `μ` an expansion of every stage into terminal stages (`exists_terminalExpansion`). Merges and
absorbs are one-stage steps with `b = 0`; a surgery step has one stage per capped component and
`b` its incidence cycle rank.
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

private theorem oIso_trans {A B C : ConnectedClosedOrientedManifold.{u} 3}
    (h₁ : OIso A B) (h₂ : OIso B C) : OIso A C :=
  h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

private theorem oIso_symm {A B : ConnectedClosedOrientedManifold.{u} 3} (h : OIso A B) :
    OIso B A :=
  h.elim fun f => ⟨f.symm⟩

theorem finiteConnectedSum_map_flatten (Ls : List (List (ConnectedClosedOrientedManifold.{u} 3))) :
    OIso (finiteConnectedSum (Ls.map finiteConnectedSum)) (finiteConnectedSum Ls.flatten) := by
  induction Ls with
  | nil => exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  | cons l Ls ih =>
    have h₁ : OIso (finiteConnectedSum ((l :: Ls).map finiteConnectedSum))
        (connectedSum (finiteConnectedSum l) (finiteConnectedSum (Ls.map finiteConnectedSum))) :=
      finiteConnectedSum_append [finiteConnectedSum l] (Ls.map finiteConnectedSum)
    have h₂ : OIso
        (connectedSum (finiteConnectedSum l) (finiteConnectedSum (Ls.map finiteConnectedSum)))
        (connectedSum (finiteConnectedSum l) (finiteConnectedSum Ls.flatten)) :=
      ih.elim fun g => nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
        (ClosedOrientedManifold.OrientedDiffeomorph.refl _) g
    have h₃ : OIso (finiteConnectedSum (l ++ Ls.flatten))
        (connectedSum (finiteConnectedSum l) (finiteConnectedSum Ls.flatten)) :=
      finiteConnectedSum_append l Ls.flatten
    exact oIso_trans (oIso_trans h₁ h₂) (oIso_symm h₃)

theorem finiteConnectedSum_map_flatten_append
    (Ls : List (List (ConnectedClosedOrientedManifold.{u} 3)))
    (K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    OIso (finiteConnectedSum (Ls.map finiteConnectedSum ++ K))
      (finiteConnectedSum (Ls.flatten ++ K)) := by
  have h₁ := finiteConnectedSum_append (Ls.map finiteConnectedSum) K
  have h₂ := finiteConnectedSum_append Ls.flatten K
  have h₃ : OIso
      (connectedSum (finiteConnectedSum (Ls.map finiteConnectedSum)) (finiteConnectedSum K))
      (connectedSum (finiteConnectedSum Ls.flatten) (finiteConnectedSum K)) :=
    (finiteConnectedSum_map_flatten Ls).elim fun f =>
      nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph f
        (ClosedOrientedManifold.OrientedDiffeomorph.refl _)
  exact oIso_trans (oIso_trans h₁ h₃) (oIso_symm h₂)

theorem perm_flatten_map_append_replicate {ι : Type w} {α : Type v} (x : α) (B : ι → List α)
    (c : ι → ℕ) (l : List ι) :
    ((l.map fun i => B i ++ List.replicate (c i) x).flatten).Perm
      ((l.map B).flatten ++ List.replicate (l.map c).sum x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons, List.replicate_add,
      List.append_assoc]
    refine List.Perm.append_left (B a) ?_
    refine (List.Perm.append_left (List.replicate (c a) x) ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

variable {S : Type v} (carrier : S → ConnectedClosedOrientedManifold.{u} 3)
  (X : ConnectedClosedOrientedManifold.{u} 3) (prot : S → Type w) (pred : ∀ s, prot s → Prop)

structure Expansion (G : S → Prop) (s : S) where
  Index : Type w
  stage : Index → S
  enum : List Index
  nodup : enum.Nodup
  complete : ∀ i, i ∈ enum
  count : ℕ
  good : ∀ i, G (stage i)
  reconstruction : OIso (finiteConnectedSum (enum.map (carrier ∘ stage) ++ List.replicate count X))
    (carrier s)
  seam : prot s ≃ Σ i, prot (stage i)
  seam_pred : ∀ p, pred s p ↔ pred (stage (seam p).1) (seam p).2

namespace Expansion

variable {carrier X prot pred}

def refl {G : S → Prop} {s : S} (h : G s) : Expansion carrier X prot pred G s where
  Index := PUnit
  stage _ := s
  enum := [PUnit.unit]
  nodup := List.nodup_singleton _
  complete _ := List.mem_singleton.mpr rfl
  count := 0
  good _ := h
  reconstruction := ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  seam := (Equiv.uniqueSigma fun _ : PUnit => prot s).symm
  seam_pred _ := Iff.rfl

def mono {G G' : S → Prop} (hG : ∀ t, G t → G' t) {s : S}
    (E : Expansion carrier X prot pred G s) : Expansion carrier X prot pred G' s where
  Index := E.Index
  stage := E.stage
  enum := E.enum
  nodup := E.nodup
  complete := E.complete
  count := E.count
  good i := hG _ (E.good i)
  reconstruction := E.reconstruction
  seam := E.seam
  seam_pred := E.seam_pred

def bind {G G' : S → Prop} {s : S} (E : Expansion carrier X prot pred G s)
    (F : ∀ i, Expansion carrier X prot pred G' (E.stage i)) :
    Expansion carrier X prot pred G' s where
  Index := Σ i, (F i).Index
  stage p := (F p.1).stage p.2
  enum := E.enum.flatMap fun i => (F i).enum.map (Sigma.mk i)
  nodup := by
    refine List.nodup_flatMap.mpr ⟨fun i _ => ((F i).nodup.map sigma_mk_injective), ?_⟩
    refine E.nodup.imp fun {i i'} hne => ?_
    intro p hp hp'
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hp
    obtain ⟨m', -, he⟩ := List.mem_map.mp hp'
    exact hne (congrArg Sigma.fst he).symm
  complete p := List.mem_flatMap.mpr ⟨p.1, E.complete p.1,
    List.mem_map.mpr ⟨p.2, (F p.1).complete p.2, rfl⟩⟩
  count := (E.enum.map fun i => (F i).count).sum + E.count
  good p := (F p.1).good p.2
  reconstruction := by
    let A : E.Index → List (ConnectedClosedOrientedManifold.{u} 3) := fun i =>
      (F i).enum.map (carrier ∘ (F i).stage) ++ List.replicate (F i).count X
    let B : E.Index → List (ConnectedClosedOrientedManifold.{u} 3) := fun i =>
      (F i).enum.map (carrier ∘ (F i).stage)
    have h₁ : OIso (finiteConnectedSum (E.enum.map (fun i => finiteConnectedSum (A i)) ++
        List.replicate E.count X))
        (finiteConnectedSum (E.enum.map (carrier ∘ E.stage) ++ List.replicate E.count X)) := by
      refine finiteConnectedSum_congr (List.rel_append ?_ (List.forall₂_same.mpr fun _ _ =>
        ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩))
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun i _ => (F i).reconstruction
    have h₂ : OIso (finiteConnectedSum (E.enum.map (fun i => finiteConnectedSum (A i)) ++
        List.replicate E.count X))
        (finiteConnectedSum ((E.enum.map A).flatten ++ List.replicate E.count X)) := by
      have := finiteConnectedSum_map_flatten_append (E.enum.map A) (List.replicate E.count X)
      rwa [List.map_map] at this
    have hp : ((E.enum.map A).flatten ++ List.replicate E.count X).Perm
        ((E.enum.flatMap fun i => (F i).enum.map (Sigma.mk i)).map
          (carrier ∘ fun p : (Σ i, (F i).Index) => (F p.1).stage p.2) ++
          List.replicate ((E.enum.map fun i => (F i).count).sum + E.count) X) := by
      have he : (E.enum.flatMap fun i => (F i).enum.map (Sigma.mk i)).map
          (carrier ∘ fun p : (Σ i, (F i).Index) => (F p.1).stage p.2) = (E.enum.map B).flatten := by
        simp only [List.flatMap_def, List.map_flatten, List.map_map]
        refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
        simp only [Function.comp_apply, List.map_map]
        rfl
      rw [he, List.replicate_add, ← List.append_assoc]
      exact List.Perm.append_right _ (perm_flatten_map_append_replicate X B (fun i => (F i).count)
        E.enum)
    exact oIso_trans (oIso_symm (finiteConnectedSum_perm hp))
      (oIso_trans (oIso_symm h₂) (oIso_trans h₁ E.reconstruction))
  seam := E.seam.trans ((Equiv.sigmaCongrRight fun i => (F i).seam).trans
    (Equiv.sigmaAssoc fun i m => prot ((F i).stage m)).symm)
  seam_pred p := (E.seam_pred p).trans ((F (E.seam p).1).seam_pred (E.seam p).2)

end Expansion

theorem exists_terminalExpansion (μ : S → ℕ) (Terminal : S → Prop)
    (step : ∀ s, ¬ Terminal s →
      Nonempty (Expansion carrier X prot pred (fun t => μ t < μ s) s)) (s : S) :
    Nonempty (Expansion carrier X prot pred Terminal s) := by
  suffices h : ∀ n, ∀ s, μ s = n → Nonempty (Expansion carrier X prot pred Terminal s) from
    h _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn
    by_cases hs : Terminal s
    · exact ⟨Expansion.refl hs⟩
    obtain ⟨E⟩ := step s hs
    exact ⟨E.bind fun i => Classical.choice (ih _ (hn ▸ E.good i) _ rfl)⟩

end GC.Seifert.RelativeNormalization
