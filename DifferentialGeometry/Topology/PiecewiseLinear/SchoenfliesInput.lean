import DifferentialGeometry.Topology.PiecewiseLinear.SimplyEmbedded
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
structure IsPLDiskDecomposition (K : Geometry.SimplicialComplex ℝ E)
    (cells : Finset (Set E)) : Prop where
  finite_faces : K.faces.Finite
  isPLBall : IsPLBall 2 K.space
  cell_isPLBall : ∀ C ∈ cells, IsPLBall 2 C
  cell_space : ∀ C ∈ cells, (restrict K C).space = C
  space_eq : K.space = ⋃ C ∈ cells, C
  inter_subset_boundary : ∀ C ∈ cells, ∀ D ∈ cells, C ≠ D →
    C ∩ D ⊆ (boundaryComplex 2 (restrict K C)).space
  inter_isPLBall : ∀ C ∈ cells, ∀ D ∈ cells, C ≠ D → (C ∩ D).Nonempty →
    IsPLBall 0 (C ∩ D) ∨ IsPLBall 1 (C ∩ D)

open Classical in
def IsFreeDiskCell (K : Geometry.SimplicialComplex ℝ E) (C : Set E) : Prop :=
  IsPLBall 1 ((boundaryComplex 2 (restrict K C)).space ∩ (boundaryComplex 2 K).space)

theorem IsPLDiskDecomposition.cell_subset {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) {C : Set E}
    (hC : C ∈ cells) : C ⊆ K.space := by
  rw [h.space_eq]
  exact subset_iUnion_of_subset C (subset_iUnion_of_subset hC Subset.rfl)

theorem IsPLDiskDecomposition.cells_nonempty {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) : cells.Nonempty := by
  obtain ⟨x, hx⟩ := h.isPLBall.nonempty
  rw [h.space_eq] at hx
  obtain ⟨C, hC, _⟩ := mem_iUnion₂.mp hx
  exact ⟨C, hC⟩

open Classical in
theorem IsPLDiskDecomposition.inter_subset_boundaries {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) {C D : Set E}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D) :
    C ∩ D ⊆ (boundaryComplex 2 (restrict K C)).space ∩
      (boundaryComplex 2 (restrict K D)).space := by
  refine subset_inter (h.inter_subset_boundary C hC D hD hne) ?_
  rw [inter_comm]
  exact h.inter_subset_boundary D hD C hC hne.symm

open Classical in
structure SchoenfliesInput : Prop where
  isSimplyEmbedded_frontier_of_convex :
    ∀ C : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ C → IsPLBall 3 C →
      IsSimplyEmbedded (frontier C)
  isSimplyEmbedded_frontier_coneComplex :
    ∀ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (p : EuclideanSpace ℝ (Fin 3)) (hL : IsConeBase p L),
      L.faces.Finite → IsPLBall 2 L.space → IsSimplyEmbedded (frontier (coneComplex hL).space)
  isSimplyEmbedded_union_sdiff_diskInterior :
    ∀ (S₁ S₂ D : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (r : ℝ),
      IsSimplyEmbedded S₁ → IsSimplyEmbedded S₂ →
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D →
      ℓ ≠ 0 → D ⊆ {x | ℓ x = r} → S₁ ∩ S₂ = D →
      IsSimplyEmbedded ((S₁ ∪ S₂) \ (D \ (f '' stdSimplexBoundary 2)))
  exists_two_free_disk_cells :
    ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (cells : Finset (Set (EuclideanSpace ℝ (Fin 3)))),
      IsPLDiskDecomposition K cells → 1 < cells.card →
      ∃ C ∈ cells, ∃ D ∈ cells, C ≠ D ∧ IsFreeDiskCell K C ∧ IsFreeDiskCell K D

theorem SchoenfliesInput.exists_free_disk_cell_ne (I : SchoenfliesInput)
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
    {cells : Finset (Set (EuclideanSpace ℝ (Fin 3)))}
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    (C₀ : Set (EuclideanSpace ℝ (Fin 3))) :
    ∃ C ∈ cells, C ≠ C₀ ∧ IsFreeDiskCell K C := by
  obtain ⟨C, hC, D, hD, hne, hfreeC, hfreeD⟩ := I.exists_two_free_disk_cells K cells h hmore
  by_cases hCC₀ : C = C₀
  · exact ⟨D, hD, hCC₀ ▸ hne.symm, hfreeD⟩
  · exact ⟨C, hC, hCC₀, hfreeC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
