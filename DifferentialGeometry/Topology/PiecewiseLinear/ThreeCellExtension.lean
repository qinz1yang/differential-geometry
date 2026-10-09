/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_extension_of_threeCell
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F}
    {fP : (Fin 4 → ℝ) → E} {fQ : (Fin 4 → ℝ) → F}
    (hfP : IsPLHomeomorphOn fP (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) P)
    (hfQ : IsPLHomeomorphOn fQ (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) Q) {g : E → F}
    (hg : IsPLHomeomorphOn g (fP '' stdSimplexBoundary 3) (fQ '' stdSimplexBoundary 3)) :
    ∃ G : E → F, IsPLHomeomorphOn G P Q ∧ EqOn G g (fP '' stdSimplexBoundary 3) :=
  exists_isPLHomeomorphOn_of_stdSimplexBoundary (n := 2) hfP hfQ hg

end DifferentialGeometry.Topology.PiecewiseLinear
