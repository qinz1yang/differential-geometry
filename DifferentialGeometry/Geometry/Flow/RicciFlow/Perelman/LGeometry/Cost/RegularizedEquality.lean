import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lCost_eq_lRegularizedCostC1
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M)
    (tau : ℝ) (htau : 0 ≤ tau) :
    lCost S T x y tau = lRegularizedCostC1 S T 0 (Real.sqrt tau) x y := by
  unfold lCost lRegularizedCostC1
  simp_rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ tau htau]

end DifferentialGeometry.PDE.RicciFlow.Perelman
