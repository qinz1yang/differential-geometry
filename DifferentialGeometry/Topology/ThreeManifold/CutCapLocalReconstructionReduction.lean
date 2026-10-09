import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private def tubeBasePoint :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2 :=
  (⟨EuclideanSpace.single 0 1, by simp⟩, ⟨0, by norm_num⟩)

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_cutIndices_ne_empty_of_nonempty_index (h : Nonempty E.tubes.Index) :
    ∃ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ := by
  obtain ⟨a⟩ := h
  refine ⟨ConnectedComponents.mk (E.tubes.tube a tubeBasePoint), fun hcut => ?_⟩
  have hmem : a ∈ E.cutIndices (ConnectedComponents.mk (E.tubes.tube a tubeBasePoint)) :=
    (E.mem_cutIndices_iff_exists_tube_mem_componentSet _ a).mpr
      ⟨tubeBasePoint, by
        rw [ClosedOrientedManifold.componentSet_mk]
        exact mem_connectedComponent⟩
  rw [hcut] at hmem
  exact Finset.notMem_empty a hmem

theorem isEmpty_index_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : IsEmpty E.tubes.Index :=
  ⟨fun a => (E.exists_cutIndices_ne_empty_of_nonempty_index ⟨a⟩).elim fun C hC => hC (h C)⟩

theorem cutComponentGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) : E.cutComponentGluing :=
  fun C hne => absurd (h C) hne

theorem exists_singleton_associatedFactors_of_isEmpty_index [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) :
    ∃ N : ConnectedClosedOrientedManifold.{u} 3, E.associatedFactors C = {N} :=
  E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C
    (E.cutIndices_eq_empty_of_isEmpty_index C)

theorem ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    (E.associatedFactors C).ncard = 1 ∨ (E.associatedFactors C).ncard = 2 := by
  have hle := E.ncard_associatedFactors_le_card_cutIndices_add_one C
  have hpos : 0 < (E.associatedFactors C).ncard :=
    (Set.ncard_pos (E.associatedFactors_finite C)).mpr (E.associatedFactors_nonempty C)
  omega

theorem sphericalGraphSumRealization_singleTube_dichotomy
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.sphericalGraphSumRealization S)
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ [S])).toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  rcases E.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one C hcard with h1 | h2
  · left
    have hcyc : E.incidenceCycleRank C = 1 := by
      rw [incidenceCycleRank, hcard, h1]
    have hC := h C
    rw [hcyc] at hC
    simpa using hC
  · right
    have hcyc : E.incidenceCycleRank C = 0 := by
      rw [incidenceCycleRank, hcard, h2]
    have hC := h C
    rw [hcyc] at hC
    simpa using hC

theorem localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) : E.localReconstruction :=
  E.localReconstruction_of_incidenceGluing (fun C => E.cutIncidenceGraph_connected C)
    (E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hr hglue hcount)

theorem exists_summandCompletion_of_cutIndices_eq_empty (hr : E.NoTubeRealization)
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L ∧ (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) ∧
        K.length = (E.cutIndices C).card + 1 - L.length := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, hKlen, hKfac, hdiff⟩ :=
    E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC L hL
  exact ⟨L, K, hL, hKfac, hdiff, hKlen⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  fun i =>
    (T.transition i).localReconstruction_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      (hr i) (hglue i) (hcount i)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
