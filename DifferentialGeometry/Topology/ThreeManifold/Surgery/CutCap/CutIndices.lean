import DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutIndices_ne_empty_iff_exists_tube_mem_componentSet
    (C : ConnectedComponents M.Carrier) :
    E.cutIndices C ≠ ∅ ↔
      ∃ a : E.tubes.Index,
        ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
          E.tubes.tube a z ∈ ClosedOrientedManifold.componentSet M C := by
  rw [← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mp ha⟩
  · rintro ⟨a, z, hz⟩
    exact ⟨a, (E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mpr ⟨z, hz⟩⟩

theorem forall_cutIndices_ne_empty_iff_forall_exists_tube_mem_componentSet :
    (∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) ↔
      ∀ C : ConnectedComponents M.Carrier,
        ∃ a : E.tubes.Index,
          ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
            E.tubes.tube a z ∈ ClosedOrientedManifold.componentSet M C :=
  forall_congr' fun C => E.cutIndices_ne_empty_iff_exists_tube_mem_componentSet C

theorem forall_cutIndices_ne_empty_of_nonempty_index [PreconnectedSpace M.Carrier]
    (h : Nonempty E.tubes.Index) :
    ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ := by
  obtain ⟨a⟩ := h
  intro C
  have hmem : E.tubes.tube a (sphereBasePoint, ⟨0, by norm_num⟩) ∈
      ClosedOrientedManifold.componentSet M C := by
    rw [ClosedOrientedManifold.mem_componentSet]
    exact Subsingleton.elim _ _
  refine fun hcut => Finset.notMem_empty a ?_
  exact hcut ▸ (E.mem_cutIndices_iff_exists_tube_mem_componentSet C a).mpr ⟨_, hmem⟩

theorem not_isEmpty_index_of_forall_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅) :
    Nonempty E.tubes.Index := by
  obtain ⟨x⟩ := E.source_nonempty
  obtain ⟨a, -⟩ := Finset.nonempty_iff_ne_empty.mpr (h (ConnectedComponents.mk x))
  exact ⟨a⟩

theorem ncard_associatedFactors_eq_one_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    (E.associatedFactors C).ncard = 1 := by
  obtain ⟨b, hb⟩ := SimpleGraph.exists_nat_add_card_eq_card_add_one_of_ends (E.cutEnds C)
    (by simpa [cutIncidenceGraph] using E.cutIncidenceGraph_connected C)
  have hcard : (E.cutIndices C).card = 0 := by rw [hC]; simp
  have hb' : b + (E.associatedFactors C).ncard = 1 := by
    rw [Nat.card_coe_set_eq, Fintype.card_coe, hcard] at hb
    simpa using hb
  have hpos : 0 < (E.associatedFactors C).ncard :=
    (Set.ncard_pos (E.associatedFactors_finite C)).mpr (E.associatedFactors_nonempty C)
  omega

theorem cutIndices_ne_empty_of_two_le_ncard_associatedFactors
    (C : ConnectedComponents M.Carrier) (h : 2 ≤ (E.associatedFactors C).ncard) :
    E.cutIndices C ≠ ∅ :=
  fun hC => absurd (E.ncard_associatedFactors_eq_one_of_cutIndices_eq_empty C hC) (by omega)

theorem componentConnectedSumDecomposition_of_forall_cutIndices_ne_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  (E.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty h).mpr
    (E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined hglue hcount)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
