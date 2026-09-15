import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open Classical in
theorem IsPLDiskDecomposition.of_isSubdivision
    {K R : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hR : IsSubdivision R K) (hfin : R.faces.Finite) :
    IsPLDiskDecomposition R cells := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite R.faces := hfin.to_subtype
  have hsub (C : Set E) (hC : C ∈ cells) :
      IsSubdivision (restrict R C) (restrict K C) := by
    have hs := hR.restrict (restrict K C) (restrict_faces_subset K C)
    rwa [h.cell_space C hC] at hs
  refine ⟨hfin, hR.space_eq.symm ▸ h.isPLBall, h.cell_isPLBall,
    fun C hC => (hsub C hC).space_eq.trans (h.cell_space C hC),
    hR.space_eq.trans h.space_eq, ?_, h.inter_isPLBall⟩
  intro C hC D hD hne
  let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
  let _ : Finite (restrict R C).faces := (restrict_faces_finite R C).to_subtype
  rw [boundaryComplex_space_of_isSubdivision (restrict K C) (restrict R C)
    ((h.cell_space C hC).symm ▸ (h.cell_isPLBall C hC)).isCombinatorialManifoldWithBoundary
    (hsub C hC)]
  exact h.inter_subset_boundary C hC D hD hne

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open Classical in
theorem IsPLDiskDecomposition.isFreeDiskCell_iff_of_isSubdivision
    {K R : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) (hR : IsSubdivision R K) (hfin : R.faces.Finite)
    {C : Set E} (hC : C ∈ cells) : IsFreeDiskCell R C ↔ IsFreeDiskCell K C := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite R.faces := hfin.to_subtype
  let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
  let _ : Finite (restrict R C).faces := (restrict_faces_finite R C).to_subtype
  have hs := hR.restrict (restrict K C) (restrict_faces_subset K C)
  rw [h.cell_space C hC] at hs
  unfold IsFreeDiskCell
  rw [boundaryComplex_space_of_isSubdivision K R h.isPLBall.isCombinatorialManifoldWithBoundary hR,
    boundaryComplex_space_of_isSubdivision (restrict K C) (restrict R C)
      ((h.cell_space C hC).symm ▸ (h.cell_isPLBall C hC)).isCombinatorialManifoldWithBoundary hs]

open Classical in
theorem IsPLDiskDecomposition.image
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells)
    (hL : L.faces.Finite) {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space)
    (hcell : ∀ C ∈ cells, (restrict L (f '' C)).space = f '' C) :
    IsPLDiskDecomposition L (cells.image (fun C => f '' C)) := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite L.faces := hL.to_subtype
  have hmap (C : Set E) (hC : C ∈ cells) :
      IsPLHomeomorphOn f (restrict K C).space (restrict L (f '' C)).space := by
    rw [h.cell_space C hC, hcell C hC]
    exact hf.restrict (h.cell_isPLBall C hC).isPolyhedron (h.cell_subset hC)
  have hbd (C : Set E) (hC : C ∈ cells) :
      (boundaryComplex 2 (restrict L (f '' C))).space =
        f '' (boundaryComplex 2 (restrict K C)).space := by
    let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
    let _ : Finite (restrict L (f '' C)).faces := (restrict_faces_finite L (f '' C)).to_subtype
    exact boundaryComplex_space_of_isPLHomeomorphOn (restrict K C) (restrict L (f '' C))
      ((h.cell_space C hC).symm ▸ (h.cell_isPLBall C hC)).isCombinatorialManifoldWithBoundary
      (hmap C hC)
  refine ⟨hL, h.isPLBall.of_isPLHomeomorphOn hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact (h.cell_isPLBall D hD).of_isPLHomeomorphOn
      (hf.restrict (h.cell_isPLBall D hD).isPolyhedron (h.cell_subset hD))
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact hcell D hD
  · rw [← hf.bijOn.image_eq, h.space_eq]
    simp only [image_iUnion]
    ext y
    simp only [mem_iUnion, mem_image, Finset.mem_image]
    constructor
    · rintro ⟨C, hC, x, hx, rfl⟩
      exact ⟨f '' C, ⟨C, hC, rfl⟩, x, hx, rfl⟩
    · rintro ⟨_, ⟨C, hC, rfl⟩, x, hx, rfl⟩
      exact ⟨C, hC, x, hx, rfl⟩
  · intro C hC D hD hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    have hAB : A ≠ B := fun heq => hne (heq ▸ rfl)
    rw [← hf.bijOn.injOn.image_inter (h.cell_subset hA) (h.cell_subset hB), hbd A hA]
    exact image_mono (h.inter_subset_boundary A hA B hB hAB)
  · intro C hC D hD hne hCD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    have hAB : A ≠ B := fun heq => hne (heq ▸ rfl)
    rw [← hf.bijOn.injOn.image_inter (h.cell_subset hA) (h.cell_subset hB)] at hCD ⊢
    have hpoly := (h.cell_isPLBall A hA).isPolyhedron.inter (h.cell_isPLBall B hB).isPolyhedron
    have hmapAB := hf.restrict hpoly (inter_subset_left.trans (h.cell_subset hA))
    rcases h.inter_isPLBall A hA B hB hAB hCD.of_image with hball | hball
    · exact Or.inl (hball.of_isPLHomeomorphOn hmapAB)
    · exact Or.inr (hball.of_isPLHomeomorphOn hmapAB)

open Classical in
theorem IsPLDiskDecomposition.isFreeDiskCell_image_iff
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells)
    (hL : L.faces.Finite) {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space)
    {C : Set E} (hC : C ∈ cells) (hcell : (restrict L (f '' C)).space = f '' C) :
    IsFreeDiskCell L (f '' C) ↔ IsFreeDiskCell K C := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  let _ : Finite L.faces := hL.to_subtype
  let _ : Finite (restrict K C).faces := (restrict_faces_finite K C).to_subtype
  let _ : Finite (restrict L (f '' C)).faces := (restrict_faces_finite L (f '' C)).to_subtype
  have hmap : IsPLHomeomorphOn f (restrict K C).space (restrict L (f '' C)).space := by
    rw [h.cell_space C hC, hcell]
    exact hf.restrict (h.cell_isPLBall C hC).isPolyhedron (h.cell_subset hC)
  have hbd := boundaryComplex_space_of_isPLHomeomorphOn (restrict K C) (restrict L (f '' C))
    ((h.cell_space C hC).symm ▸ (h.cell_isPLBall C hC)).isCombinatorialManifoldWithBoundary hmap
  have hCK : (boundaryComplex 2 (restrict K C)).space ⊆ K.space :=
    (boundaryComplex_space_subset 2 (restrict K C)).trans
      ((h.cell_space C hC).subset.trans (h.cell_subset hC))
  unfold IsFreeDiskCell
  rw [hbd, boundaryComplex_space_of_isPLHomeomorphOn K L h.isPLBall.isCombinatorialManifoldWithBoundary hf,
    ← hf.bijOn.injOn.image_inter hCK (boundaryComplex_space_subset 2 K)]
  let _ : Finite (boundaryComplex 2 K).faces :=
    (h.finite_faces.subset (boundaryComplex_faces_subset 2 K)).to_subtype
  let _ : Finite (boundaryComplex 2 (restrict K C)).faces :=
    ((restrict_faces_finite K C).subset (boundaryComplex_faces_subset 2 (restrict K C))).to_subtype
  have hpoly : IsPolyhedron ((boundaryComplex 2 (restrict K C)).space ∩
      (boundaryComplex 2 K).space) := (isPolyhedron_space _).inter (isPolyhedron_space _)
  have hmapI := hf.restrict hpoly (inter_subset_left.trans hCK)
  exact ⟨fun hb => hb.of_isPLHomeomorphOn hmapI.symm,
    fun hb => hb.of_isPLHomeomorphOn hmapI⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
open Classical in
theorem IsPLDiskDecomposition.card_image
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) {f : E → F} (hf : InjOn f K.space) :
    (cells.image (fun C => f '' C)).card = cells.card := by
  apply Finset.card_image_iff.mpr
  intro C hC D hD heq
  exact (hf.image_eq_image_iff (h.cell_subset hC) (h.cell_subset hD)).mp heq

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open Classical in
theorem IsPLDiskDecomposition.exists_planar_image
    {K : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (h : IsPLDiskDecomposition K cells) :
    ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (f : E → EuclideanSpace ℝ (Fin 2)),
      L.faces.Finite ∧ IsPLHomeomorphOn f K.space L.space ∧
      IsPLDiskDecomposition L (cells.image (fun C => f '' C)) ∧
      (cells.image (fun C => f '' C)).card = cells.card ∧
      ∀ C ∈ cells, IsFreeDiskCell L (f '' C) ↔ IsFreeDiskCell K C := by
  let _ : Finite K.faces := h.finite_faces.to_subtype
  obtain ⟨A, Q, φ, ψ, hA, hAfin, hQfin, _, hiso⟩ :=
    exists_isSubdivision_isGlueIso_planar K h.isPLBall
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  let f := simplicialMap A φ
  have hf : IsPLHomeomorphOn f K.space Q.space := by
    rw [← hA.space_eq]
    exact hiso.isPLHomeomorphOn
  obtain ⟨L, hL, hLfin, hcells⟩ := exists_isSubdivision_subcomplexes Q
    (fun C : cells => f '' C.1)
    (fun C => (h.cell_isPLBall C.1 C.2).isPolyhedron.image_of_isPiecewiseAffineOn
      (hf.isPiecewiseAffineOn.mono_of_isPolyhedron (h.cell_isPLBall C.1 C.2).isPolyhedron
        (h.cell_subset C.2)) (hf.bijOn.injOn.mono (h.cell_subset C.2)))
    (fun C => (image_mono (h.cell_subset C.2)).trans hf.bijOn.image_eq.subset)
  have hfL : IsPLHomeomorphOn f K.space L.space := hL.space_eq.symm ▸ hf
  have hcell (C : Set E) (hC : C ∈ cells) : (restrict L (f '' C)).space = f '' C :=
    restrict_space_of_eq_biUnion L (f '' C) (hcells ⟨C, hC⟩)
  exact ⟨L, f, hLfin, hfL, h.image hLfin hfL hcell, h.card_image hf.bijOn.injOn,
    fun C hC => h.isFreeDiskCell_image_iff hLfin hfL hC (hcell C hC)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
