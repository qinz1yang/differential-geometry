import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLDiskDecomposition_of_cover
    {P : Set E} (hP : IsPLBall 2 P) (cells : Finset (Set E))
    (hcell : ∀ C ∈ cells, IsPLBall 2 C) (hcover : P = ⋃ C ∈ cells, C)
    (hinter : ∀ C ∈ cells, ∀ D ∈ cells, C ≠ D → (C ∩ D).Nonempty →
      IsPLBall 0 (C ∩ D) ∨ IsPLBall 1 (C ∩ D)) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      IsPLDiskDecomposition K cells := by
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hsub (C : Set E) (hC : C ∈ cells) : C ⊆ P := by
    rw [hcover]
    exact subset_iUnion_of_subset C (subset_iUnion_of_subset hC Subset.rfl)
  obtain ⟨L, hLK, hLfin, hpieces⟩ := exists_isSubdivision_subcomplexes K
    (fun C : cells => (C : Set E)) (fun C => (hcell C C.property).isPolyhedron)
    (fun C => by rw [hKP]; exact hsub C C.property)
  let _ : Finite L.faces := hLfin.to_subtype
  have hLP : L.space = P := hLK.space_eq.trans hKP
  have hL : IsPLBall 2 L.space := hLP.symm ▸ hP
  have hspaces (C : Set E) (hC : C ∈ cells) : (restrict L C).space = C :=
    restrict_space_of_eq_biUnion L C (hpieces ⟨C, hC⟩)
  refine ⟨L, hLfin, hLP, hLfin, hL, hcell, hspaces, hLP.trans hcover, ?_, hinter⟩
  intro C hC D hD hne x hx
  let _ : Finite (restrict L C).faces := (restrict_faces_finite L C).to_subtype
  have hA : IsPLBall 2 (restrict L C).space := (hspaces C hC).symm ▸ hcell C hC
  have hbd := inter_closure_sdiff_subset_boundaryComplex L (restrict L C)
    hL.isCombinatorialManifoldWithBoundary hA.isCombinatorialManifoldWithBoundary
    (space_mono_of_faces_subset (restrict_faces_subset L C))
  rw [hspaces C hC] at hbd
  have hdiff : D \ (C ∩ D) = D \ C := by
    ext y
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hdense : closure (D \ C) = D := by
    rw [← hdiff]
    rcases hinter C hC D hD hne ⟨x, hx⟩ with hI | hI
    · exact (hcell D hD).closure_sdiff_eq_of_isPLBall hI inter_subset_right (by decide)
    · exact (hcell D hD).closure_sdiff_eq_of_isPLBall hI inter_subset_right (by decide)
  have hDL : D ⊆ L.space := by rw [hLP]; exact hsub D hD
  exact hbd ⟨hx.1, closure_mono (sdiff_subset_sdiff_left hDL) (hdense.symm.subset hx.2)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
