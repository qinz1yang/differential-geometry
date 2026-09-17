import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_extension_of_threeCell
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F}
    {fP : (Fin 4 → ℝ) → E} {fQ : (Fin 4 → ℝ) → F}
    (hfP : IsPLHomeomorphOn fP (stdSimplex ℝ (Fin 4)) P)
    (hfQ : IsPLHomeomorphOn fQ (stdSimplex ℝ (Fin 4)) Q) {g : E → F}
    (hg : IsPLHomeomorphOn g (fP '' stdSimplexBoundary 3) (fQ '' stdSimplexBoundary 3)) :
    ∃ G : E → F, IsPLHomeomorphOn G P Q ∧ EqOn G g (fP '' stdSimplexBoundary 3) :=
  exists_isPLHomeomorphOn_of_stdSimplexBoundary (n := 2) hfP hfQ hg

end DifferentialGeometry.Topology.PiecewiseLinear
