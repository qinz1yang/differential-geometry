/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSurfaceTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem geometricLink_barycentricSubdivision_singleton
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E}
    (hp : {p} ∈ K.faces) :
    SimplicialComplex.geometricLink (barycentricSubdivision K) {p} = upperLink K {p} := by
  have hnhds : (dualCell K {p} hp).space ∈ 𝓝[(barycentricSubdivision K).space] p := by
    rw [← closedStar_barycentricSubdivision_eq_dualCell K hp]
    exact closedStar_mem_nhdsWithin _ _
  calc
    SimplicialComplex.geometricLink (barycentricSubdivision K) {p} =
        SimplicialComplex.geometricLink (dualCell K {p} hp) {p} :=
      (geometricLink_eq_of_space_mem_nhdsWithin (dualCell_faces_subset K hp) hnhds).symm
    _ = upperLink K {p} := by
      simpa only [Finset.centroid_singleton, id_eq] using geometricLink_dualCell K hp

open Classical in
theorem boundaryComplex_barycentricSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    boundaryComplex (n + 1) (barycentricSubdivision K) =
      barycentricSubdivision (boundaryComplex (n + 1) K) := by
  let _ : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  apply eq_of_faces_subset_of_space_eq _ _ (barycentricSubdivision K)
    (boundaryComplex_faces_subset (n + 1) _)
    (barycentricSubdivision_faces_subset (boundaryComplex_faces_subset (n + 1) K))
  rw [boundaryComplex_space_of_isSubdivision K _ hK (barycentricSubdivision_isSubdivision K),
    (barycentricSubdivision_isSubdivision (boundaryComplex (n + 1) K)).space_eq]

open Classical in
theorem boundaryComplex_upperLink_singleton [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {p : E}
    (hp : {p} ∈ (boundaryComplex (n + 1) K).faces) :
    boundaryComplex n (upperLink K {p}) = upperLink (boundaryComplex (n + 1) K) {p} := by
  let _ : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  rw [← geometricLink_barycentricSubdivision_singleton K
    (boundaryComplex_faces_subset (n + 1) K hp),
    ← geometricLink_boundaryComplex n (barycentricSubdivision K) p,
    boundaryComplex_barycentricSubdivision K hK,
    geometricLink_barycentricSubdivision_singleton _ hp]

open Classical in
theorem boundaryComplex_derivedNeighborhoodCellBase [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ (boundaryComplex (n + 1) K).faces) :
    boundaryComplex n (derivedNeighborhoodCellBase K s) =
      derivedNeighborhoodCellBase (boundaryComplex (n + 1) K) s := by
  let _ : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  have hv : {s.centroid ℝ id} ∈
      (boundaryComplex (n + 1) (barycentricSubdivision K)).faces := by
    rw [boundaryComplex_barycentricSubdivision K hK]
    exact singleton_centroid_mem_barycentricSubdivision _ hs
  change boundaryComplex n (upperLink (barycentricSubdivision K) {s.centroid ℝ id}) = _
  rw [boundaryComplex_upperLink_singleton _ hK.barycentricSubdivision hv,
    boundaryComplex_barycentricSubdivision K hK]
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
