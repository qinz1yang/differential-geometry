/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchEndChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLBoundaryTubeProducer_double
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    IsPLBoundaryTubeProducer (double 3 K).space :=
  isPLBoundaryTubeProducer_of_exists_endChart (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
    (exists_endChart_of_mem_boundary (double 3 K) (isCombinatorialManifold_double_succ_succ K hK))

end DifferentialGeometry.Topology.PiecewiseLinear
