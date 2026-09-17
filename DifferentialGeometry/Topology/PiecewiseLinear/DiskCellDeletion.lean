import DifferentialGeometry.Topology.PiecewiseLinear.RelativeFreeDiskCell
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLDiskDecomposition.isFreeDiskCell_iff_isPLBall_inter_boundaryComplex
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) {C : Set E} (hC : C ∈ cells) :
    IsFreeDiskCell K C ↔ IsPLBall 1 (C ∩ (boundaryComplex 2 K).space) := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
  have hA : IsPLBall 2 (restrict K C).space := (h.cell_space C hC).symm ▸ h.cell_isPLBall C hC
  have hsub := inter_boundaryComplex_space_subset K (restrict K C)
    h.isPLBall.isCombinatorialManifoldWithBoundary hA.isCombinatorialManifoldWithBoundary
    (restrict_faces_subset K C)
  rw [h.cell_space C hC] at hsub
  have heq : (boundaryComplex 2 (restrict K C)).space ∩ (boundaryComplex 2 K).space =
      C ∩ (boundaryComplex 2 K).space := by
    apply Subset.antisymm
    · exact inter_subset_inter_left _ ((boundaryComplex_space_subset 2 (restrict K C)).trans_eq (h.cell_space C hC))
    · exact fun _ hx => ⟨hsub hx, hx.2⟩
  exact congrArg (IsPLBall 1) heq |>.to_iff

theorem IsPLDiskDecomposition.closure_sdiff_cell_eq_biUnion_erase
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) {C : Set E} (hC : C ∈ cells) :
    closure (K.space \ C) = ⋃ A ∈ cells.erase C, A := by
  classical
  have hclosed : IsClosed (⋃ A ∈ cells.erase C, A) := (cells.erase C).finite_toSet.isClosed_biUnion
    (fun A hA => (h.cell_isPLBall A (Finset.mem_of_mem_erase hA)).isPolyhedron.isClosed)
  apply Subset.antisymm
  · apply closure_minimal _ hclosed
    rintro x ⟨hxK, hxC⟩
    rw [h.space_eq] at hxK
    obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hxK
    exact mem_iUnion₂.mpr ⟨A, Finset.mem_erase.mpr ⟨fun hAC => hxC (hAC ▸ hxA), hA⟩, hxA⟩
  · refine iUnion₂_subset fun A hA => ?_
    have hAmem : A ∈ cells := Finset.mem_of_mem_erase hA
    have hne : A ≠ C := (Finset.mem_erase.mp hA).1
    have hdense : closure (A \ C) = A := by
      by_cases hmeet : (A ∩ C).Nonempty
      · have hdiff : A \ (A ∩ C) = A \ C := by
          ext x
          simp only [mem_sdiff, mem_inter_iff]
          tauto
        rcases h.inter_isPLBall A hAmem C hC hne hmeet with hI | hI
        · simpa only [hdiff] using (h.cell_isPLBall A hAmem).closure_sdiff_eq_of_isPLBall
            hI inter_subset_left (by decide)
        · simpa only [hdiff] using (h.cell_isPLBall A hAmem).closure_sdiff_eq_of_isPLBall
            hI inter_subset_left (by decide)
      · have hdiff : A \ C = A := by
          ext x
          exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxC => hmeet ⟨x, hx, hxC⟩⟩⟩
        rw [hdiff, (h.cell_isPLBall A hAmem).isPolyhedron.isClosed.closure_eq]
    exact hdense.symm.subset.trans (closure_mono (sdiff_subset_sdiff_left (h.cell_subset hAmem)))

open Classical in
theorem IsPLDiskDecomposition.erase_of_isFreeDiskCell
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) {C : Set E} (hC : C ∈ cells) (hfree : IsFreeDiskCell K C) :
    IsPLDiskDecomposition (restrict K (closure (K.space \ C))) (cells.erase C) := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  have hball := isPLBall_closure_sdiff_of_inter_boundaryComplex K h.isPLBall (h.cell_isPLBall C hC)
    (h.cell_subset hC) ((h.isFreeDiskCell_iff_isPLBall_inter_boundaryComplex hC).mp hfree)
  exact h.restrict_cells (Finset.erase_subset C cells) (h.closure_sdiff_cell_eq_biUnion_erase hC) hball

omit [FiniteDimensional ℝ E] in
open Classical in
def IsFreeDiskCellDeletion (D : Set E)
    (P Q : Geometry.SimplicialComplex ℝ E × Finset (Set E)) : Prop :=
  IsPLDiskDecomposition P.1 P.2 ∧ ∃ C ∈ P.2, ¬C ⊆ D ∧ IsFreeDiskCell P.1 C ∧
    Q.1 = restrict P.1 (closure (P.1.space \ C)) ∧ Q.2 = P.2.erase C

theorem IsPLDiskDecomposition.exists_free_disk_cell_deletion_sequence
    {K : Geometry.SimplicialComplex ℝ E} {cells subcells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hsub : subcells ⊆ cells)
    {D : Set E} (hD : IsPLBall 2 D) (hcover : D = ⋃ C ∈ subcells, C) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (cs : Finset (Set E)),
      IsPLDiskDecomposition L cs ∧ L.space = D ∧ subcells ⊆ cs ∧ cs ⊆ cells ∧
        Relation.ReflTransGen (IsFreeDiskCellDeletion D) (K, cells) (L, cs) := by
  classical
  induction cells using Finset.strongInductionOn generalizing K with
  | _ cells ih =>
    by_cases heq : D = K.space
    · exact ⟨K, cells, h, heq.symm, hsub, Subset.rfl, Relation.ReflTransGen.refl⟩
    obtain ⟨C, hC, hnot, hfree⟩ := h.exists_free_disk_cell_not_subset hsub hD hcover heq
    have hCnot : C ∉ subcells := by
      intro hCs
      apply hnot
      rw [hcover]
      exact subset_iUnion_of_subset C (subset_iUnion_of_subset hCs Subset.rfl)
    have hsub' : subcells ⊆ cells.erase C := by
      intro A hA
      exact Finset.mem_erase.mpr ⟨fun hAC => hCnot (hAC ▸ hA), hsub hA⟩
    let R := restrict K (closure (K.space \ C))
    have hR : IsPLDiskDecomposition R (cells.erase C) := h.erase_of_isFreeDiskCell hC hfree
    obtain ⟨L, cs, hL, hLD, hsubcs, hcs, hsequence⟩ :=
      ih (cells.erase C) (Finset.erase_ssubset hC) hR hsub'
    refine ⟨L, cs, hL, hLD, hsubcs, hcs.trans (Finset.erase_subset C cells), ?_⟩
    have hstep : IsFreeDiskCellDeletion D (K, cells) (R, cells.erase C) :=
      ⟨h, C, hC, hnot, hfree, rfl, rfl⟩
    exact (Relation.ReflTransGen.single hstep).trans hsequence

end DifferentialGeometry.Topology.PiecewiseLinear
