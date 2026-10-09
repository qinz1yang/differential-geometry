import DifferentialGeometry.Topology.ThreeManifold.CutCapFactorNormalization
import DifferentialGeometry.Topology.ThreeManifold.CutCapNoTubeReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

noncomputable def canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    List (ConnectedClosedOrientedManifold.{u} 3) :=
  Classical.choose (E.exists_completeEnumeration C)

theorem completeEnumeration_canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    E.CompleteEnumeration C (E.canonicalEnumeration C) :=
  Classical.choose_spec (E.exists_completeEnumeration C)

theorem length_canonicalEnumeration (C : ConnectedComponents M.Carrier) :
    (E.canonicalEnumeration C).length = (E.associatedFactors C).ncard :=
  (E.ncard_associatedFactors_eq_length (E.completeEnumeration_canonicalEnumeration C)).symm

def graphSumRealization : Prop :=
  ∀ C : ConnectedComponents M.Carrier,
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

def sphericalGraphSumRealization (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents M.Carrier,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold)

def cutGraphSumRealization : Prop :=
  ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

theorem graphSumRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.graphSumRealization :=
  fun C => E.length_eq_incidenceCycleRank_of_componentConnectedSumDecomposition h
    (E.completeEnumeration_canonicalEnumeration C)

theorem componentConnectedSumDecomposition_of_graphSumRealization
    (h : E.graphSumRealization) : E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun {L L'} hp => finiteConnectedSum_perm hp) ?_
  intro C
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨E.canonicalEnumeration C, E.completeEnumeration_canonicalEnumeration C, K,
    by
      have hb := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [E.length_canonicalEnumeration C]
      omega,
    hKfac, hdiff⟩

theorem graphSumRealization_iff_componentConnectedSumDecomposition :
    E.graphSumRealization ↔ E.componentConnectedSumDecomposition :=
  ⟨E.componentConnectedSumDecomposition_of_graphSumRealization,
    E.graphSumRealization_of_componentConnectedSumDecomposition⟩

theorem graphSumRealization_iff_localReconstruction :
    E.graphSumRealization ↔ E.localReconstruction :=
  E.graphSumRealization_iff_componentConnectedSumDecomposition.trans
    E.localReconstruction_iff_componentConnectedSumDecomposition.symm

theorem graphSumRealization_iff_noTubeRealization_and_cutComponentRealization :
    E.graphSumRealization ↔ E.NoTubeRealization ∧ E.cutComponentRealization :=
  E.graphSumRealization_iff_componentConnectedSumDecomposition.trans
    E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization

theorem graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization :
    E.graphSumRealization ↔ E.NoTubeRealization ∧ E.cutGraphSumRealization := by
  constructor
  · intro h
    exact ⟨E.noTubeRealization_of_componentConnectedSumDecomposition
        (E.componentConnectedSumDecomposition_of_graphSumRealization h),
      fun C _ => h C⟩
  · rintro ⟨hr, hcut⟩ C
    by_cases hC : E.cutIndices C = ∅
    · obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
        E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC
          (E.canonicalEnumeration C) (E.completeEnumeration_canonicalEnumeration C)
      refine ⟨K, ?_, hKfac, hdiff⟩
      have hle := E.ncard_associatedFactors_le_card_cutIndices_add_one C
      have hsum := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [hKlen, E.length_canonicalEnumeration C]
      omega
    · exact hcut C hC

theorem sphericalGraphSumRealization_of_componentConnectedSumDecomposition
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.componentConnectedSumDecomposition) : E.sphericalGraphSumRealization S := by
  intro C
  have hb : E.incidenceCycleRank C + (E.canonicalEnumeration C).length =
      (E.cutIndices C).card + 1 := by
    rw [E.length_canonicalEnumeration C, E.incidenceCycleRank_add_ncard_associatedFactors C]
  exact (E.componentConnectedSumDecomposition_iff_fixedSphericalModel S hS).mp h C
    (E.canonicalEnumeration C) (E.incidenceCycleRank C)
    (E.completeEnumeration_canonicalEnumeration C) hb

theorem componentConnectedSumDecomposition_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.componentConnectedSumDecomposition := by
  refine E.componentConnectedSumDecomposition_of_singleEnumeration
    (fun {L L'} hp => finiteConnectedSum_perm hp) ?_
  intro C
  exact ⟨E.canonicalEnumeration C, E.completeEnumeration_canonicalEnumeration C,
    List.replicate (E.incidenceCycleRank C) S,
    by
      have hb := E.incidenceCycleRank_add_ncard_associatedFactors C
      rw [List.length_replicate, E.length_canonicalEnumeration C]
      omega,
    fun F hF => by
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
      exact hS,
    h C⟩

theorem sphericalGraphSumRealization_iff_componentConnectedSumDecomposition
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.sphericalGraphSumRealization S ↔ E.componentConnectedSumDecomposition :=
  ⟨E.componentConnectedSumDecomposition_of_sphericalGraphSumRealization S hS,
    E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS⟩

theorem sphericalGraphSumRealization_iff_of_isSphereTwoTimesCircleFactor
    (S S' : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) (hS' : isSphereTwoTimesCircleFactor S') :
    E.sphericalGraphSumRealization S ↔ E.sphericalGraphSumRealization S' :=
  (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).trans
    (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S' hS').symm

theorem graphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) : E.graphSumRealization :=
  E.graphSumRealization_of_componentConnectedSumDecomposition
    (E.componentConnectedSumDecomposition_of_isEmpty_index hr)

theorem sphericalGraphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) : E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_isEmpty_index hr)

theorem exists_ne_nil_of_incidenceCycleRank_pos (h : E.graphSumRealization)
    (C : ConnectedComponents M.Carrier) (hpos : 0 < E.incidenceCycleRank C) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K ≠ [] ∧ K.length = E.incidenceCycleRank C ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) := by
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C
  exact ⟨K, fun hnil => by rw [hnil, List.length_nil] at hKlen; omega, hKlen, hKfac, hdiff⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_graphSumRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).graphSumRealization :=
  forall_congr' fun i =>
    ((T.transition i).graphSumRealization_iff_componentConnectedSumDecomposition).symm

theorem componentConnectedSumDecomposition_iff_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).sphericalGraphSumRealization S :=
  forall_congr' fun i =>
    ((T.transition i).sphericalGraphSumRealization_iff_componentConnectedSumDecomposition
      S hS).symm

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutGraphSumRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      (∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization) ∧
        (∀ i : Fin T.eventCount, (T.transition i).cutGraphSumRealization) :=
  (T.componentConnectedSumDecomposition_iff_graphSumRealization).trans
    ((forall_congr' fun i =>
      (T.transition i).graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization).trans
      forall_and)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
