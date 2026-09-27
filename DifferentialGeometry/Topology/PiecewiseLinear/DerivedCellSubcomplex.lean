/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
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
