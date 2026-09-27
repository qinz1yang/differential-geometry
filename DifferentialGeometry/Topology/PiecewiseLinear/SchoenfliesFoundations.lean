/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskGluing
import DifferentialGeometry.Topology.PiecewiseLinear.FreeDiskCell

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem schoenflies_input : SchoenfliesInput where
  isSimplyEmbedded_frontier_of_convex _ hconv hball :=
    PiecewiseLinear.isSimplyEmbedded_frontier_of_convex hconv hball
  isSimplyEmbedded_frontier_coneComplex L _ hp hfinite hL := by
    let _ : Finite L.faces := hfinite.to_subtype
    exact PiecewiseLinear.isSimplyEmbedded_frontier_coneComplex L hp hL
  isSimplyEmbedded_union_sdiff_diskInterior _ _ _ _ ℓ _ hS₁ hS₂ hq hℓ hDr hD :=
    isSimplyEmbedded_union_sdiff_diskInterior_of_subset_fiber hS₁ hS₂ hq ℓ hℓ hDr hD
  exists_two_free_disk_cells _ _ h hmore := h.exists_two_free_disk_cells hmore

end DifferentialGeometry.Topology.PiecewiseLinear
