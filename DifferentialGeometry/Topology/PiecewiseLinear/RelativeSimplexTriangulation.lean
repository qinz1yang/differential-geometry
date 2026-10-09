/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexRefinement
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem restrict_closure_sdiff_space_of_restrict_space
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {Q : Set E}
    (hQ : (restrict K Q).space = Q) :
    (restrict K (closure (K.space \ Q))).space = closure (K.space \ Q) := by
  let C := subcomplexGeneratedBy K (restrict K Q).facesᶜ
  have hC : closure (K.space \ Q) = C.space := by
    rw [← hQ]
    exact closure_space_sdiff_space_eq_subcomplexGeneratedBy K K (restrict K Q)
      Subset.rfl (restrict_faces_subset K Q)
  refine Subset.antisymm (restrict_space_subset K _) ?_
  rw [hC]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := C.mem_space_iff.mp hx
  exact (restrict K C.space).convexHull_subset_space
    ⟨subcomplexGeneratedBy_faces_subset K _ hs, C.convexHull_subset_space hs⟩ hxs

open Classical in
theorem exists_isSubdivision_restrict_space_preserving_subcomplex_of_mem_nhdsWithin
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    {P : Set E} (hP : IsPolyhedron P)
    (hregular : closure (K.space \ closure (K.space \ P)) = P)
    (hnhds : ∀ x ∈ A.space, P ∈ 𝓝[K.space] x) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ (restrict R P).space = P := by
  let Q := closure (K.space \ P)
  have hQ : IsPolyhedron Q := (isPolyhedron_space K).closure_sdiff hP
  have hQK : Q ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hAQ : A.space ⊆ Qᶜ := by
    intro x hx hxQ
    obtain ⟨U, hU, hUP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hnhds x hx)
    obtain ⟨y, hyU, hyK, hyP⟩ := mem_closure_iff_nhds.mp hxQ U hU
    exact hyP (hUP ⟨hyU, hyK⟩)
  obtain ⟨R₀, hR₀, hfin₀, hAR₀, hstar⟩ :=
    exists_isSubdivision_regularNeighborhoodIn_subset_of_isOpen K A hA hQ.isClosed.isOpen_compl hAQ
  let _ : Finite R₀.faces := hfin₀.to_subtype
  have hQR₀ : Q ⊆ R₀.space := hR₀.space_eq.symm ▸ hQK
  have hdis : Disjoint (regularNeighborhoodIn R₀ A.space).space Q :=
    Set.disjoint_left.mpr fun _ hx hy => hstar hx hy
  obtain ⟨R, hR, hfinR, hAR, hRQ⟩ :=
    exists_isSubdivision_restrict_space_preserving_subcomplex R₀ A hAR₀ hQ hQR₀ hdis
  let _ : Finite R.faces := hfinR.to_subtype
  have hRK : IsSubdivision R K := hR.trans hR₀
  have heq : closure (R.space \ Q) = P := by rw [hRK.space_eq]; exact hregular
  refine ⟨R, hRK, hfinR, hAR, ?_⟩
  have h := restrict_closure_sdiff_space_of_restrict_space R hRQ
  rwa [heq] at h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_triangulation_derivedNeighborhood
    {n : ℕ} (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces) :
    ∃ T : Geometry.SimplicialComplex ℝ E, T.faces.Finite ∧ A.faces ⊆ T.faces ∧
      T.space = (PiecewiseLinear.derivedNeighborhood K A).space ∧
      IsCombinatorialManifoldWithBoundary (n + 1) T ∧
      (boundaryComplex (n + 1) T).space =
        (boundaryComplex (n + 1) (PiecewiseLinear.derivedNeighborhood K A)).space := by
  let N := PiecewiseLinear.derivedNeighborhood K A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K A).to_subtype
  have hN : IsCombinatorialManifoldWithBoundary (n + 1) N := hK.derivedNeighborhood A
  have hNK : N.space ⊆ K.space := derivedNeighborhood_space_subset K A
  obtain ⟨R, hR, hfinR, hAR, hRN⟩ :=
    exists_isSubdivision_restrict_space_preserving_subcomplex_of_mem_nhdsWithin K A hA
      (isPolyhedron_space N) (hK.closure_sdiff_closure_sdiff_eq K N hN hNK)
      (fun _ hx => derivedNeighborhood_mem_nhdsWithin hA hx)
  let _ : Finite R.faces := hfinR.to_subtype
  let T := restrict R N.space
  have hfinT : T.faces.Finite := restrict_faces_finite R N.space
  let _ : Finite T.faces := hfinT.to_subtype
  have hAT : A.faces ⊆ T.faces := by
    intro s hs
    refine ⟨hAR hs, fun x hx => ?_⟩
    exact mem_of_mem_nhdsWithin (space_mono_of_faces_subset hA (A.convexHull_subset_space hs hx))
      (derivedNeighborhood_mem_nhdsWithin hA (A.convexHull_subset_space hs hx))
  have hid : IsPLHomeomorphOn id N.space T.space := by
    rw [hRN]
    exact (isPolyhedron_space N).isPLHomeomorphOn_id
  refine ⟨T, hfinT, hAT, hRN, hN.of_isPLHomeomorphOn hid, ?_⟩
  simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn N T hN hid

open Classical in
structure DerivedNeighborhoodTriangulation
    (K A : Geometry.SimplicialComplex ℝ E) where
  complex : Geometry.SimplicialComplex ℝ E
  finite_faces : complex.faces.Finite
  faces_subset : A.faces ⊆ complex.faces
  space_eq : complex.space = (derivedNeighborhood K A).space

open Classical in
noncomputable def IsCombinatorialManifoldWithBoundary.derivedNeighborhoodTriangulation
    {n : ℕ} (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces) :
    DerivedNeighborhoodTriangulation K A := by
  let h := hK.exists_triangulation_derivedNeighborhood K A hA
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1⟩

open Classical in
theorem DerivedNeighborhoodTriangulation.isCombinatorialManifoldWithBoundary
    {n : ℕ} {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    IsCombinatorialManifoldWithBoundary (n + 1) T.complex := by
  let _ : Finite (derivedNeighborhood K A).faces :=
    (derivedNeighborhood_faces_finite K A).to_subtype
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  apply (hK.derivedNeighborhood A).of_isPLHomeomorphOn (f := id)
  rw [T.space_eq]
  exact (isPolyhedron_space (derivedNeighborhood K A)).isPLHomeomorphOn_id

open Classical in
theorem DerivedNeighborhoodTriangulation.boundaryComplex_space
    {n : ℕ} {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    (boundaryComplex (n + 1) T.complex).space =
      (boundaryComplex (n + 1) (derivedNeighborhood K A)).space := by
  let N := derivedNeighborhood K A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K A).to_subtype
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hid : IsPLHomeomorphOn id N.space T.complex.space := by
    rw [T.space_eq]
    exact (isPolyhedron_space N).isPLHomeomorphOn_id
  simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn N T.complex
    (hK.derivedNeighborhood A) hid

open Classical in
noncomputable def DerivedNeighborhoodTriangulation.strongDeformationRetract
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A) (hA : A.faces ⊆ K.faces) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      {x : T.complex.space | (x : E) ∈ A.space} := by
  rw [T.space_eq]
  exact derivedNeighborhoodStrongDeformationRetract hA

end DifferentialGeometry.Topology.PiecewiseLinear
