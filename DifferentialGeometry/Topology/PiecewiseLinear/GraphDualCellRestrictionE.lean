/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CutExhaustion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem graphDualCell_space_eq_inter_dualCell (K L : Geometry.SimplicialComplex ℝ E)
    {v : E} (hv : {v} ∈ K.faces) :
    (graphDualCell K L v).space = (derivedNeighborhood K L).space ∩
      (dualCell K {v} hv).space := by
  rw [graphDualCell_space_eq_inter K L hv,
    closedStar_barycentricSubdivision_eq_dualCell K hv]

open Classical in
theorem graphDualCell_restrict_core_eq (K S L : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) (hL : L.faces ⊆ K.faces) (v : E) :
    graphDualCell S (restrict L S.space) v = graphDualCell S L v := by
  unfold graphDualCell
  rw [derivedNeighborhood_restrict_core_eq K S L hS hL]

end DifferentialGeometry.Topology.PiecewiseLinear
