import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem componentConnectedSumDecomposition_of_cutIndices_eq_empty
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) (hL : E.CompleteEnumeration C L) :
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      K.length = (E.cutIndices C).card + 1 - L.length ∧
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  obtain ⟨ρ⟩ := hr C N hC hN
  obtain ⟨N', hL'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  have hNN' : N' = N := by
    have hmem : N' ∈ L := by rw [hL']; exact List.mem_singleton.mpr rfl
    have h := hL.2.1 N' hmem
    rw [hN, Set.mem_singleton_iff] at h
    exact h
  refine ⟨[], by rw [hL']; simp [hC], by simp, ?_⟩
  rw [hL', hNN']
  exact ⟨ρ⟩

def cutComponentRealization : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

def cutComponentSingleEnumeration : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L ∧
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

theorem cutComponentRealization_iff_singleEnumeration :
    E.cutComponentRealization ↔ E.cutComponentSingleEnumeration := by
  constructor
  · intro h C hC
    obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
    obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C hC L hL
    exact ⟨L, K, hL, hKlen, hKfac, hdiff⟩
  · intro h C hC L hL
    obtain ⟨L₀, K, hL₀, hKlen, hKfac, hρ⟩ := h C hC
    have hp := E.completeEnumeration_perm hL hL₀
    refine ⟨K, ?_, hKfac, ?_⟩
    · rw [hp.length_eq]
      exact hKlen
    · obtain ⟨σ⟩ := finiteConnectedSum_perm (hp.symm.append_right K)
      exact hρ.map fun ρ => ρ.trans σ

theorem cutComponentRealization_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentRealization :=
  fun C _ L hL => h C L hL

theorem cutComponentSingleEnumeration_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentSingleEnumeration :=
  E.cutComponentRealization_iff_singleEnumeration.mp
    (E.cutComponentRealization_of_componentConnectedSumDecomposition h)

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization :
    E.componentConnectedSumDecomposition ↔ E.NoTubeRealization ∧ E.cutComponentRealization := by
  constructor
  · intro h
    exact ⟨E.noTubeRealization_of_componentConnectedSumDecomposition h,
      E.cutComponentRealization_of_componentConnectedSumDecomposition h⟩
  · rintro ⟨hr, hcut⟩ C L hL
    by_cases hC : E.cutIndices C = ∅
    · exact E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC L hL
    · exact hcut C hC L hL

theorem noTubeRealization_of_forall_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) : E.NoTubeRealization :=
  fun C _ hC _ => absurd hC (h C)

theorem cutComponentRealization_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : E.cutComponentRealization :=
  fun C hne => absurd (h C) hne

theorem componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) :
    E.componentConnectedSumDecomposition ↔ E.cutComponentRealization := by
  constructor
  · exact E.cutComponentRealization_of_componentConnectedSumDecomposition
  · intro hcut
    exact E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
      ⟨E.noTubeRealization_of_forall_cutIndices_ne_empty h, hcut⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      (∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization) ∧
        (∀ i : Fin T.eventCount, (T.transition i).cutComponentRealization) :=
  (forall_congr' fun i =>
    (T.transition i).componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization).trans
    forall_and

end FiniteCutCapTrace

end DifferentialGeometry.Topology
