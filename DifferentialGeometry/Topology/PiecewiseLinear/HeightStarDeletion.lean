import DifferentialGeometry.Topology.PiecewiseLinear.DiskCellDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.HeightStarDecomposition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_free_disk_cell_deletion_sequence_to_closedStar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hreg : closure (interior K.space) = K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) {p : E} (hp : {p} ∈ K.faces)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = ℓ p})) :
    ∃ L R : Geometry.SimplicialComplex ℝ E,
      IsPLDiskDecomposition L (heightSectionCells 2 K ℓ (ℓ p)) ∧
      L.space = K.space ∩ {x | ℓ x = ℓ p} ∧
      IsPLDiskDecomposition R ((heightSectionCells 2 K ℓ (ℓ p)).filter (fun C => C ⊆ closedStar K p)) ∧
      R.space = closedStar K p ∩ {x | ℓ x = ℓ p} ∧
      Relation.ReflTransGen (IsFreeDiskCellDeletion (closedStar K p ∩ {x | ℓ x = ℓ p}))
        (L, heightSectionCells 2 K ℓ (ℓ p))
        (R, (heightSectionCells 2 K ℓ (ℓ p)).filter (fun C => C ⊆ closedStar K p)) := by
  classical
  obtain ⟨L, _, hLspace, hL⟩ := exists_isPLDiskDecomposition_heightSectionCells K hdim hreg ℓ hinj (ℓ p) hD
  have hcover := biUnion_heightSectionCells_subset_closedStar_eq K hdim hreg ℓ hinj hp hD
  obtain ⟨R, cs, hR, hRspace, hsub, hcs, hsequence⟩ := hL.exists_free_disk_cell_deletion_sequence
    (Finset.filter_subset (fun C => C ⊆ closedStar K p) _)
    (isPLBall_closedStar_inter_fiber K hp ℓ hD) hcover.symm
  have heq : cs = (heightSectionCells 2 K ℓ (ℓ p)).filter (fun C => C ⊆ closedStar K p) := by
    apply Finset.Subset.antisymm _ hsub
    intro C hC
    refine Finset.mem_filter.mpr ⟨hcs hC, ?_⟩
    intro x hx
    exact (hRspace ▸ hR.cell_subset hC hx).1
  rw [heq] at hR hsequence
  exact ⟨L, R, hL, hLspace, hR, hRspace, hsequence⟩

end DifferentialGeometry.Topology.PiecewiseLinear
