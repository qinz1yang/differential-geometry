import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SimpleGraph

theorem exists_nat_add_card_eq_card_add_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hconn : G.Connected) :
    ∃ b : ℕ, b + Fintype.card V = Fintype.card G.edgeSet + 1 := by
  have hle : Fintype.card V ≤ Fintype.card G.edgeSet + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hconn.card_vert_le_card_edgeSet_add_one
  exact ⟨Fintype.card G.edgeSet + 1 - Fintype.card V, by omega⟩

theorem exists_nat_add_card_eq_card_add_one_of_ends {V I : Type*} [Fintype I]
    (ends : I → Sym2 V)
    (hconn : (SimpleGraph.fromRel fun a b : V => ∃ i, ends i = s(a, b)).Connected) :
    ∃ b : ℕ, b + Nat.card V = Fintype.card I + 1 := by
  classical
  set G := SimpleGraph.fromRel fun a b : V => ∃ i, ends i = s(a, b)
  have hsub : G.edgeSet ⊆ Set.range ends := by
    rintro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
      rcases he with ⟨-, ⟨i, hi⟩ | ⟨i, hi⟩⟩
      · exact ⟨i, hi⟩
      · exact ⟨i, hi.trans Sym2.eq_swap⟩
  have h1 : Nat.card G.edgeSet ≤ Nat.card (Set.range ends) :=
    Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
  have h2 : Nat.card (Set.range ends) ≤ Nat.card I := by
    refine Nat.card_le_card_of_surjective
      (fun i : I => (⟨ends i, ⟨i, rfl⟩⟩ : Set.range ends)) ?_
    rintro ⟨y, i, rfl⟩
    exact ⟨i, rfl⟩
  have h3 : Nat.card V ≤ Nat.card G.edgeSet + 1 := hconn.card_vert_le_card_edgeSet_add_one
  have hI : Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
  refine ⟨Fintype.card I + 1 - Nat.card V, ?_⟩
  omega

end SimpleGraph

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def sphereBasePoint : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem mem_cutIndices_iff_exists_tube_mem_componentSet (C : ConnectedComponents M.Carrier)
    (a : E.tubes.Index) :
    a ∈ E.cutIndices C ↔
      ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
        E.tubes.tube a z ∈ ClosedOrientedManifold.componentSet M C := by
  classical
  constructor
  · intro ha
    exact ⟨(sphereBasePoint, ⟨0, by norm_num⟩), (Finset.mem_filter.mp ha).2 _⟩
  · rintro ⟨z₀, hz₀⟩
    have hz₀' : ConnectedComponents.mk (E.tubes.tube a z₀) = C := hz₀
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun z => ?_⟩
    rw [ClosedOrientedManifold.mem_componentSet]
    have hcont : Continuous fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Set.Icc (-2 : ℝ) 2 => ConnectedComponents.mk (E.tubes.tube a z) :=
      ConnectedComponents.continuous_coe.comp (E.tubes.tube a).continuous
    have hpre : IsPreconnected (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Set.Icc (-2 : ℝ) 2)) := by
      have hicc : PreconnectedSpace ↥(Set.Icc (-2 : ℝ) 2) :=
        isPreconnected_iff_preconnectedSpace.mp (isPreconnected_Icc (a := (-2 : ℝ)) (b := 2))
      simpa only [Set.univ_prod_univ] using isPreconnected_univ.prod isPreconnected_univ
    have hconst : ConnectedComponents.mk (E.tubes.tube a z₀) =
        ConnectedComponents.mk (E.tubes.tube a z) :=
      (hpre.image _ hcont.continuousOn).subsingleton ⟨z₀, trivial, rfl⟩ ⟨z, trivial, rfl⟩
    rw [← hconst]
    exact hz₀'

theorem mk_coreBoundarySphere_eq (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ConnectedComponents.mk (E.tubes.coreBoundarySphere (a.1, side) z).1 = C := by
  classical
  have ha := (Finset.mem_filter.mp a.2).2
  have hz : E.tubes.boundarySphere (a.1, side) z ∈
      ClosedOrientedManifold.componentSet M C :=
    ha (z, SphericalTubeSystem.boundaryLevel side)
  have hval : (E.tubes.coreBoundarySphere (a.1, side) z).1 =
      E.tubes.boundarySphere (a.1, side) z := rfl
  rw [hval]
  exact hz

def cutCoreComponent (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cappedCutComponents C :=
  ⟨ConnectedComponents.mk (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a.1, side) z)),
    E.tubes.coreBoundarySphere (a.1, side) z,
    E.mk_coreBoundarySphere_eq C a side z, rfl⟩

theorem cutCoreComponent_eq (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cutCoreComponent C a side z = E.cutCoreComponent C a side z' := by
  refine Subtype.ext ?_
  have hcont : Continuous fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ConnectedComponents.mk (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a.1, side) z)) :=
    ConnectedComponents.continuous_coe.comp
      (E.capping.coreInclusion.continuous.comp
        (E.tubes.coreBoundarySphere (a.1, side)).continuous)
  exact (isPreconnected_univ.image _ hcont.continuousOn).subsingleton
    ⟨z, trivial, rfl⟩ ⟨z', trivial, rfl⟩

def cutEndFactor (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ↥(E.associatedFactors C) :=
  ⟨E.cappedFactor C (E.cutCoreComponent C a side z), by
    rw [E.associatedFactors_eq_range_cappedFactor]
    exact ⟨E.cutCoreComponent C a side z, rfl⟩⟩

theorem cutEndFactor_eq (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (side : Bool) (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    E.cutEndFactor C a side z = E.cutEndFactor C a side z' := by
  exact Subtype.ext (congrArg (E.cappedFactor C) (E.cutCoreComponent_eq C a side z z'))

def cutEnds (C : ConnectedComponents M.Carrier) (a : E.cutIndices C) :
    Sym2 ↥(E.associatedFactors C) :=
  s(E.cutEndFactor C a false sphereBasePoint, E.cutEndFactor C a true sphereBasePoint)

def cutIncidenceGraph (C : ConnectedComponents M.Carrier) :
    SimpleGraph ↥(E.associatedFactors C) :=
  SimpleGraph.fromRel fun A B : ↥(E.associatedFactors C) =>
    ∃ a : E.cutIndices C, E.cutEnds C a = s(A, B)

theorem cutIncidenceGraph_adj (C : ConnectedComponents M.Carrier)
    (A B : ↥(E.associatedFactors C)) :
    (E.cutIncidenceGraph C).Adj A B ↔
      A ≠ B ∧ (∃ a : E.cutIndices C, E.cutEnds C a = s(A, B)) := by
  rw [cutIncidenceGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, ⟨h.choose, h.choose_spec.trans Sym2.eq_swap⟩⟩
  · exact fun h => ⟨h.1, Or.inl h.2⟩

theorem ncard_associatedFactors_eq_length {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) :
    (E.associatedFactors C).ncard = L.length := by
  classical
  have hset : E.associatedFactors C = (L.toFinset : Set _) := by
    ext N
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact ⟨fun h => hL.2.2 N h, fun h => hL.2.1 N h⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL.1]

theorem exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected
    {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hconn : (E.cutIncidenceGraph C).Connected) (hL : E.CompleteEnumeration C L) :
    ∃ b : ℕ, b + L.length = (E.cutIndices C).card + 1 := by
  obtain ⟨b, hb⟩ := SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends
    (E.cutEnds C) (by simpa [cutIncidenceGraph] using hconn)
  rw [Nat.card_coe_set_eq, E.ncard_associatedFactors_eq_length hL, Fintype.card_coe] at hb
  exact ⟨b, hb⟩

def componentConnectedSumDecomposition : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

theorem localReconstruction_of_incidenceGluing
    (hconn : ∀ C : ConnectedComponents M.Carrier, (E.cutIncidenceGraph C).Connected)
    (hsum : E.componentConnectedSumDecomposition) : E.localReconstruction := by
  intro C L hL
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := hsum C L hL
  obtain ⟨b, hb⟩ :=
    E.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected (hconn C) hL
  exact ⟨K.length, K, rfl, hKfac, by omega, hdiff⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentwise_isPoincareStandard_of_incidenceGluing
    (hconn : ∀ i : Fin T.eventCount, ∀ C : ConnectedComponents (T.stage i.castSucc).Carrier,
      ((T.transition i).cutIncidenceGraph C).Connected)
    (hsum : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsumClosed : poincareStandardSumClosed.{u}) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier :=
  T.componentwise_isPoincareStandard
    (fun i => (T.transition i).localReconstruction_of_incidenceGluing (hconn i) (hsum i))
    hctrl hext hsumClosed

end FiniteCutCapTrace

end DifferentialGeometry.Topology
