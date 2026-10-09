/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem DerivedNeighborhoodTriangulation.mem_boundaryComplex_iff
    {n : ℕ} {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces)
    {x : E} (hx : x ∈ A.space) :
    x ∈ (boundaryComplex (n + 1) T.complex).space ↔
      x ∈ (boundaryComplex (n + 1) K).space := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  have hTK : T.complex.space ⊆ K.space := by
    rw [T.space_eq]
    exact derivedNeighborhood_space_subset K A
  have hxT : x ∈ T.complex.space := space_mono_of_faces_subset T.faces_subset hx
  have hnhds : T.complex.space ∈ 𝓝[K.space] x := by
    rw [T.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin hA hx
  exact mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K T.complex hK
    (T.isCombinatorialManifoldWithBoundary hK) hTK hxT hnhds

open Classical in
theorem DerivedNeighborhoodTriangulation.inter_boundaryComplex_space
    {n : ℕ} {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces) :
    A.space ∩ (boundaryComplex (n + 1) T.complex).space =
      A.space ∩ (boundaryComplex (n + 1) K).space := by
  ext x
  exact and_congr_right fun hx => T.mem_boundaryComplex_iff hK hA hx

open Classical in
theorem DerivedNeighborhoodTriangulation.faces_subset_boundaryComplex
    {n : ℕ} {K A C : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (T : DerivedNeighborhoodTriangulation K A)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hA : A.faces ⊆ K.faces)
    (hCA : C.faces ⊆ A.faces) (hC : C.space ⊆ (boundaryComplex (n + 1) K).space) :
    C.faces ⊆ (boundaryComplex (n + 1) T.complex).faces := by
  intro s hs
  have hcent := centroid_mem_openSimplex_of_mem_faces C s hs
  have hxC : s.centroid ℝ id ∈ C.space :=
    C.convexHull_subset_space hs (openSimplex_subset_convexHull s hcent)
  have hxA := space_mono_of_faces_subset hCA hxC
  exact mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset (n + 1) T.complex)
    (T.faces_subset (hCA hs)) hcent ((T.mem_boundaryComplex_iff hK hA hxA).mpr (hC hxC))

end DifferentialGeometry.Topology.PiecewiseLinear
