/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
  {cells : Finset (Set (EuclideanSpace ℝ (Fin 2)))}

open Classical in
theorem IsPLDiskDecomposition.boundary_cell_eq_frontier
    (h : IsPLDiskDecomposition K cells) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) : (@boundaryComplex _ _ _ (Classical.decEq _) 2 (restrict K C)).space =
        frontier C := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
  have hball : IsPLBall 2 (restrict K C).space := (h.cell_space C hC).symm ▸ h.cell_isPLBall C hC
  rw [← frontier_space_eq_boundaryComplex_space hball.isCombinatorialManifoldWithBoundary,
    h.cell_space C hC]

theorem IsPLDiskDecomposition.frontier_inter_cell
    (h : IsPLDiskDecomposition K cells) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) : frontier K.space ∩ C = frontier K.space ∩ frontier C := by
  refine Subset.antisymm (fun x hx => ⟨hx.1, ?_⟩)
    (inter_subset_inter_right _ ((frontier_subset_closure.trans
      (h.cell_isPLBall C hC).isPolyhedron.isClosed.closure_eq.subset)))
  refine ⟨subset_closure hx.2, fun hxint => hx.1.2 (interior_mono (h.cell_subset hC) hxint)⟩

open Classical in
theorem IsPLDiskDecomposition.isFreeDiskCell_iff_isPLBall_frontier_inter
    (h : IsPLDiskDecomposition K cells) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) : IsFreeDiskCell K C ↔ IsPLBall 1 (frontier K.space ∩ C) := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  unfold IsFreeDiskCell
  rw [h.boundary_cell_eq_frontier hC,
    ← frontier_space_eq_boundaryComplex_space h.isPLBall.isCombinatorialManifoldWithBoundary,
    inter_comm, ← h.frontier_inter_cell hC]

theorem IsPLDiskDecomposition.disjoint_interior_cell
    (h : IsPLDiskDecomposition K cells) {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D) : Disjoint (interior C) D := by
  rw [disjoint_left]
  intro x hxC hxD
  have hx := h.inter_subset_boundary C hC D hD hne ⟨interior_subset hxC, hxD⟩
  rw [h.boundary_cell_eq_frontier hC] at hx
  exact hx.2 hxC

theorem IsPLDiskDecomposition.not_cell_subset_cell
    (h : IsPLDiskDecomposition K cells) {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D) : ¬C ⊆ D := by
  intro hsub
  obtain ⟨x, hx⟩ := (h.cell_isPLBall C hC).interior_nonempty
  exact disjoint_left.mp (h.disjoint_interior_cell hC hD hne) hx (hsub (interior_subset hx))

theorem IsPLDiskDecomposition.cell_ne_space
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C ∈ cells) : C ≠ K.space := by
  obtain ⟨A, B, hA, hB, hAB⟩ := Finset.one_lt_card_iff.mp hmore
  obtain ⟨D, hD, hDC⟩ : ∃ D ∈ cells, D ≠ C := by
    by_cases hAC : A = C
    · exact ⟨B, hB, hAC ▸ hAB.symm⟩
    · exact ⟨A, hA, hAC⟩
  intro heq
  exact h.not_cell_subset_cell hD hC hDC (heq.symm ▸ h.cell_subset hD)

theorem IsPLDiskDecomposition.frontier_cell_ne
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C ∈ cells) : frontier C ≠ frontier K.space := by
  intro heq
  have hball := h.cell_isPLBall C hC
  apply h.cell_ne_space hmore hC
  rw [← hball.closure_interior, ← h.isPLBall.closure_interior,
    hball.interior_eq_inside_frontier, h.isPLBall.interior_eq_inside_frontier, heq]

theorem IsPLDiskDecomposition.not_frontier_cell_subset
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C ∈ cells) : ¬frontier C ⊆ frontier K.space := by
  intro hsub
  exact h.frontier_cell_ne hmore hC (PlanarJordan.eq_of_isJordanCurve_of_subset
    (isJordanCurve_of_isPLSphere_one (h.cell_isPLBall C hC).isPLSphere_frontier)
    (isJordanCurve_of_isPLSphere_one h.isPLBall.isPLSphere_frontier) hsub)

theorem IsPLDiskDecomposition.not_frontier_subset_cell
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    {C : Set (EuclideanSpace ℝ (Fin 2))} (hC : C ∈ cells) : ¬frontier K.space ⊆ C := by
  intro hsub
  have hsub' : frontier K.space ⊆ frontier C := by
    intro x hx
    exact ((h.frontier_inter_cell hC).subset ⟨hx, hsub hx⟩).2
  exact h.frontier_cell_ne hmore hC (PlanarJordan.eq_of_isJordanCurve_of_subset
    (isJordanCurve_of_isPLSphere_one h.isPLBall.isPLSphere_frontier)
    (isJordanCurve_of_isPLSphere_one (h.cell_isPLBall C hC).isPLSphere_frontier) hsub').symm

open Classical in
theorem IsPLDiskDecomposition.exists_cell_ne_with_nontrivial_frontier_inter
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    {C₀ : Set (EuclideanSpace ℝ (Fin 2))} (hC₀ : C₀ ∈ cells) :
    ∃ C ∈ cells, C ≠ C₀ ∧ (frontier K.space ∩ C).Nontrivial := by
  by_contra hnone
  have hfinite (C : Set (EuclideanSpace ℝ (Fin 2))) (hC : C ∈ cells.erase C₀) :
      (frontier K.space ∩ C).Finite := by
    have hc := Finset.mem_erase.mp hC
    exact (Set.not_nontrivial_iff.mp fun htr => hnone ⟨C, hc.2, hc.1, htr⟩).finite
  let F := ⋃ C ∈ cells.erase C₀, frontier K.space ∩ C
  have hF : F.Finite := Set.Finite.biUnion (cells.erase C₀).finite_toSet hfinite
  have hsub : frontier K.space \ F ⊆ C₀ := by
    intro x hx
    have hxK : x ∈ K.space := h.isPLBall.isPolyhedron.isClosed.closure_eq ▸ frontier_subset_closure
        hx.1
    rw [h.space_eq] at hxK
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hxK
    by_cases hCC₀ : C = C₀
    · exact hCC₀ ▸ hxC
    · exact (hx.2 (mem_iUnion₂.mpr ⟨C, Finset.mem_erase.mpr ⟨hCC₀, hC⟩, hx.1, hxC⟩)).elim
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLSphere_one h.isPLBall.isPLSphere_frontier
  apply h.not_frontier_subset_cell hmore hC₀
  intro x hx
  have hcl : x ∈ closure (frontier K.space \ F) := by
    rw [← hJ]
    exact J.carrier_subset_closure_sdiff_finite hF (hJ.symm ▸ hx)
  exact closure_minimal hsub (h.cell_isPLBall C₀ hC₀).isPolyhedron.isClosed hcl

theorem IsPLDiskDecomposition.exists_two_cells_with_nontrivial_frontier_inter
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card) :
    ∃ C ∈ cells, ∃ D ∈ cells, C ≠ D ∧ (frontier K.space ∩ C).Nontrivial ∧
      (frontier K.space ∩ D).Nontrivial := by
  obtain ⟨C₀, hC₀⟩ := h.cells_nonempty
  obtain ⟨C, hC, _, htrC⟩ := h.exists_cell_ne_with_nontrivial_frontier_inter hmore hC₀
  obtain ⟨D, hD, hDC, htrD⟩ := h.exists_cell_ne_with_nontrivial_frontier_inter hmore hC
  exact ⟨C, hC, D, hD, hDC.symm, htrC, htrD⟩

theorem IsPLDiskDecomposition.finite_frontier_inter_cells_of_subset
    (h : IsPLDiskDecomposition K cells) {C D U : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D) (hCU : C ⊆ U) (hDU : D ⊆ U) :
    (frontier U ∩ (C ∩ D)).Finite := by
  by_cases hI : (C ∩ D).Nonempty
  · rcases h.inter_isPLBall C hC D hD hne hI with hpoint | harc
    · obtain ⟨p, hp⟩ := isPLBall_zero_iff.mp hpoint
      exact (hp.symm ▸ Set.toFinite ({p} : Set (EuclideanSpace ℝ (Fin 2)))).subset
          inter_subset_right
    · have hIC : C ∩ D ⊆ frontier C := by
        rw [← h.boundary_cell_eq_frontier hC]
        exact h.inter_subset_boundary C hC D hD hne
      have hID : C ∩ D ⊆ frontier D := by
        rw [← h.boundary_cell_eq_frontier hD, inter_comm]
        exact h.inter_subset_boundary D hD C hC hne.symm
      have hfinite := (isPLBall_union_and_finite_frontier_inter
        (h.cell_isPLBall C hC) (h.cell_isPLBall D hD) harc hIC hID).2
      apply hfinite.subset
      rintro x ⟨hxU, hxI⟩
      exact ⟨⟨subset_closure (Or.inl hxI.1), fun hxint =>
        hxU.2 (interior_mono (union_subset hCU hDU) hxint)⟩, hxI⟩
  · have hempty : C ∩ D = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
    rw [hempty, inter_empty]
    exact Set.finite_empty

theorem IsPLDiskDecomposition.isFreeDiskCell_of_frontier_subset_union
    (h : IsPLDiskDecomposition K cells) {C D U : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D)
    (hCU : C ⊆ U) (hDU : D ⊆ U) (hUK : U ⊆ K.space)
    (hfront : frontier U ⊆ frontier K.space ∪ C) (hfree : IsPLBall 1 (frontier U ∩ D)) :
    IsFreeDiskCell K D := by
  have hfinite := h.finite_frontier_inter_cells_of_subset hC hD hne hCU hDU
  have houter : frontier U ∩ D ⊆ frontier K.space := by
    apply (hfree.subset_closure_sdiff_finite hfinite).trans
    apply closure_minimal _ isClosed_frontier
    rintro x ⟨hx, hxnot⟩
    exact (hfront hx.1).resolve_right fun hxC => hxnot ⟨hx.1, hxC, hx.2⟩
  have heq : frontier K.space ∩ D = frontier U ∩ D := by
    refine Subset.antisymm (fun x hx => ⟨?_, hx.2⟩) (fun x hx => ⟨houter hx, hx.2⟩)
    exact ⟨subset_closure (hDU hx.2), fun hxint => hx.1.2 (interior_mono hUK hxint)⟩
  apply (h.isFreeDiskCell_iff_isPLBall_frontier_inter hD).mpr
  rwa [heq]

end DifferentialGeometry.Topology.PiecewiseLinear
