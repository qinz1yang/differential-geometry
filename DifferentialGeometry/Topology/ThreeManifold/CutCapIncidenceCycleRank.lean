import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import DifferentialGeometry.Topology.ThreeManifold.CutCapStandardReconstruction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_perm {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hp : L.Perm L') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum L').toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds) hp

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def incidenceCycleRank (C : ConnectedComponents M.Carrier) : ℕ :=
  (E.cutIndices C).card + 1 - (E.associatedFactors C).ncard

theorem ncard_associatedFactors_le_card_cutIndices_add_one
    (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).ncard ≤ (E.cutIndices C).card + 1 := by
  classical
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨b, hb⟩ :=
    E.exists_nat_add_card_eq_card_add_one_of_incidenceGraph_connected
      (E.cutIncidenceGraph_connected C) hL
  rw [E.ncard_associatedFactors_eq_length hL]
  omega

theorem incidenceCycleRank_add_ncard_associatedFactors
    (C : ConnectedComponents M.Carrier) :
    E.incidenceCycleRank C + (E.associatedFactors C).ncard =
      (E.cutIndices C).card + 1 := by
  rw [incidenceCycleRank]
  exact Nat.sub_add_cancel (E.ncard_associatedFactors_le_card_cutIndices_add_one C)

theorem incidenceCycleRank_eq_zero_iff (C : ConnectedComponents M.Carrier) :
    E.incidenceCycleRank C = 0 ↔
      (E.associatedFactors C).ncard = (E.cutIndices C).card + 1 := by
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  constructor <;> intro h' <;> omega

theorem eq_incidenceCycleRank_of_add_ncard_associatedFactors_eq
    (C : ConnectedComponents M.Carrier) {b : ℕ}
    (hb : b + (E.associatedFactors C).ncard = (E.cutIndices C).card + 1) :
    b = E.incidenceCycleRank C := by
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  omega

theorem edgeSet_subset_range_cutEnds (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).edgeSet ⊆ Set.range (E.cutEnds C) := by
  rintro e he
  induction e using Sym2.ind with
  | _ A B =>
    rw [SimpleGraph.mem_edgeSet, cutIncidenceGraph, SimpleGraph.fromRel_adj] at he
    rcases he with ⟨-, ⟨a, ha⟩ | ⟨a, ha⟩⟩
    · exact ⟨a, ha⟩
    · exact ⟨a, ha.trans Sym2.eq_swap⟩

theorem ncard_edgeSet_le_card_cutIndices (C : ConnectedComponents M.Carrier) :
    (E.cutIncidenceGraph C).edgeSet.ncard ≤ (E.cutIndices C).card := by
  refine (Set.ncard_le_ncard (E.edgeSet_subset_range_cutEnds C)).trans ?_
  have h := Nat.card_le_card_of_surjective
    (fun i : ↥(E.cutIndices C) => (⟨E.cutEnds C i, i, rfl⟩ : Set.range (E.cutEnds C)))
    (by rintro ⟨y, i, rfl⟩; exact ⟨i, rfl⟩)
  rw [Nat.card_coe_set_eq] at h
  simpa [Nat.card_eq_fintype_card, Fintype.card_coe] using h

theorem card_cutIndices_sub_ncard_edgeSet_le_incidenceCycleRank
    (C : ConnectedComponents M.Carrier) :
    (E.cutIndices C).card - (E.cutIncidenceGraph C).edgeSet.ncard ≤
      E.incidenceCycleRank C := by
  have hE := E.ncard_edgeSet_le_card_cutIndices C
  have hV : (E.associatedFactors C).ncard ≤
      (E.cutIncidenceGraph C).edgeSet.ncard + 1 := by
    simpa using (E.cutIncidenceGraph_connected C).card_vert_le_card_edgeSet_add_one
  have hcyc := E.incidenceCycleRank_add_ncard_associatedFactors C
  omega

theorem localReconstruction_iff_componentConnectedSumDecomposition :
    E.localReconstruction ↔ E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_localReconstruction_of_incidenceGraph_connected
    fun C => E.cutIncidenceGraph_connected C

theorem length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C L hL
  refine ⟨K, ?_, hKfac, hdiff⟩
  rw [hKlen, incidenceCycleRank, ← E.ncard_associatedFactors_eq_length hL]

theorem exists_orientedDiffeomorph_finiteConnectedSum_of_length_eq_card_cutIndices_add_one
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hlen : L.length = (E.cutIndices C).card + 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, -, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hKlen0 : K.length = 0 := by
    rw [hKlen, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL, hlen]
    simp
  have hK : K = [] := List.length_eq_zero_iff.mp hKlen0
  subst hK
  simpa using hdiff

theorem exists_isSphereTwoTimesCircleFactor_of_length_eq_card_cutIndices
    (h : E.componentConnectedSumDecomposition) {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hlen : L.length = (E.cutIndices C).card) :
    ∃ F : ConnectedClosedOrientedManifold.{u} 3,
      isSphereTwoTimesCircleFactor F ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ [F])).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hK1 : K.length = 1 := by
    rw [hKlen, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL, hlen]
    omega
  obtain ⟨F, hF⟩ := List.length_eq_one_iff.mp hK1
  refine ⟨F, hKfac F ?_, ?_⟩
  · rw [hF]
    exact List.mem_singleton.mpr rfl
  · rw [hF] at hdiff
    exact hdiff

theorem noTubeRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.NoTubeRealization := by
  intro C N hC hN
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, hKlen, -, hdiff⟩ :=
    E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h hL
  have hKlen0 : K.length = 0 := by
    rw [hKlen, incidenceCycleRank, hC, hN, Set.ncard_singleton]
    simp
  have hK : K = [] := List.length_eq_zero_iff.mp hKlen0
  subst hK
  rw [List.append_nil] at hdiff
  obtain ⟨N', hL'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  have hNN : N' = N := by
    have hmem : N' ∈ L := by rw [hL']; exact List.mem_singleton.mpr rfl
    have hmem' := hL.2.1 N' hmem
    rw [hN, Set.mem_singleton_iff] at hmem'
    exact hmem'
  rw [hL', hNN] at hdiff
  simpa using hdiff

theorem cutIndices_eq_empty_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) : E.cutIndices C = ∅ :=
  Finset.not_nonempty_iff_eq_empty.mp fun h => h.elim fun a _ => isEmptyElim a

theorem incidenceCycleRank_eq_zero_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) : E.incidenceCycleRank C = 0 := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C
    (E.cutIndices_eq_empty_of_isEmpty_index C)
  rw [incidenceCycleRank, E.cutIndices_eq_empty_of_isEmpty_index C, hN, Set.ncard_singleton]
  simp

theorem componentConnectedSumDecomposition_of_exists_singleEnumeration
    (h : ∀ C : ConnectedComponents M.Carrier,
      ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
        E.CompleteEnumeration C L ∧
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun hp => finiteConnectedSum_perm hp) ?_
  intro C
  obtain ⟨L, K, hL, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨L, hL, K, hKlen, hKfac, hdiff⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem localReconstruction_of_componentConnectedSumDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) :
    ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).mpr (h i)

theorem componentConnectedSumDecomposition_of_exists_singleEnumeration
    (h : ∀ (i : Fin T.eventCount) (C : ConnectedComponents (T.stage i.castSucc).Carrier),
      ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
        (T.transition i).CompleteEnumeration C L ∧
        K.length = ((T.transition i).cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          ((T.stage i.castSucc).component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).componentConnectedSumDecomposition_of_exists_singleEnumeration
    (fun C => h i C)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
