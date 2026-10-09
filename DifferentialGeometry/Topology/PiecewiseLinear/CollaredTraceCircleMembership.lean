/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere {L T G : Set E3}
    (hL : HasFiniteCollaredTrace L T) (hG : IsPLSphere 1 G) (hsub : G ⊆ L ∩ T) :
    G ∈ traceCircles L T := by
  obtain ⟨x, hx⟩ := hG.nonempty
  have hGT : G ⊆ T := hsub.trans inter_subset_right
  have hself : G ∈ traceCircles G T := by
    refine ⟨x, ⟨hx, hGT hx⟩, ?_, hG⟩
    apply Subset.antisymm
    · exact hG.isConnected.isPreconnected.subset_connectedComponentIn hx
        (fun y hy => ⟨hy, hGT hy⟩)
    · exact (connectedComponentIn_subset _ _).trans inter_subset_left
  exact traceCircles_subset_of_inter_subset hL.traceCover
    (fun y hy => hsub hy.1) hself

end DifferentialGeometry.Topology.PiecewiseLinear
