/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood

/-!
# Derived cells restrict to subcomplexes

The derived neighbourhood cell of a face `s` is cut down by a subcomplex exactly to the
derived neighbourhood cell of `s` computed inside that subcomplex: no fullness or link
hypothesis is needed, only that every face of `L` is a face of `K` and that `s` is a face
of `L`.

The statement is specific to the *derived* cell, which is the closed star of the barycentre
of `s` in the second derived subdivision. It is false for an arbitrary cone presentation of
a neighbourhood: for the tetrahedron `K = p * σ²` and `L = ∂K`, the cone `p * σ²` meets `|L|`
in `∂(p * σ²)`, which is not a cone with apex `p` at all.

## Main results

* `derivedNeighborhoodCell_inter_subcomplex`: `|C_K(s)| ∩ |L| = |C_L(s)|`.
* `coneSet_upperLink_inter_subcomplex`: the same statement read through the cone presentation
  of the derived cell.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- **Derived cells restrict to subcomplexes.** If every face of `L` is a face of `K` and `s`
is a face of `L`, then the derived neighbourhood cell of `s` in `K`, intersected with the
polyhedron of `L`, is the derived neighbourhood cell of `s` in `L`. -/
theorem derivedNeighborhoodCell_inter_subcomplex (K L : Geometry.SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ L.space = (derivedNeighborhoodCell L s).space := by
  have hL' : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces :=
    barycentricSubdivision_faces_subset hLK
  have hcL : {s.centroid ℝ id} ∈ (barycentricSubdivision L).faces :=
    singleton_centroid_mem_barycentricSubdivision L hs
  rw [derivedNeighborhoodCell_space_eq_closedStar K (hLK hs),
    derivedNeighborhoodCell_space_eq_closedStar L hs,
    ← (barycentricSubdivision_isSubdivision L).space_eq]
  simp only [secondDerived]
  exact closedStar_barycentricSubdivision_inter_space_eq hL' hcL

open Classical in
/-- The cone reading of `derivedNeighborhoodCell_inter_subcomplex`: intersecting the cone on
the upper link of the barycentre of `s` in `K` with the polyhedron of a subcomplex `L`
containing `s` gives the cone on the corresponding upper link computed inside `L`. -/
theorem coneSet_upperLink_inter_subcomplex (K L : Geometry.SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ L.faces) :
    coneSet (s.centroid ℝ id)
          (upperLink (barycentricSubdivision K) {s.centroid ℝ id}).space ∩ L.space =
      coneSet (s.centroid ℝ id)
        (upperLink (barycentricSubdivision L) {s.centroid ℝ id}).space := by
  rw [← derivedNeighborhoodCell_space_eq_coneSet K (hLK hs),
    ← derivedNeighborhoodCell_space_eq_coneSet L hs]
  exact derivedNeighborhoodCell_inter_subcomplex K L hLK hs

end DifferentialGeometry.Topology.PiecewiseLinear
