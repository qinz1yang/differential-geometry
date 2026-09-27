/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compact_vertex_split_incidence
    {M K : Geometry.SimplicialComplex ℝ E3} (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) (e : Section34CompactEdgeIndex K K)
    {v : E3} (hw : w.1 = {v})
    (hinter : ((graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space ∩
      (splittingDisk M e.1 (hKM e.2.1)).space).Nonempty) :
    w.1 ⊆ e.1 := by
  have hv : {v} ∈ M.faces := hw ▸ hKM w.2.1
  rw [hw, Finset.singleton_subset_iff]
  exact mem_of_graphDualCell_inter_splittingDisk_nonempty M _ hv (hKM e.2.1) hinter

theorem compact_face_disk_subset_residual_ball
    {K : Geometry.SimplicialComplex ℝ E3} {N : Set E3}
    (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4)
    (hst : Section34Incident s.1 t.1) :
    closure (convexHull ℝ (s.1 : Set E3) \ N) ⊆
      closure (convexHull ℝ (t.1 : Set E3) \ N) := by
  apply closure_mono
  exact sdiff_subset_sdiff_left (convexHull_min hst (convex_convexHull ℝ _))

end DifferentialGeometry.Topology.PiecewiseLinear
