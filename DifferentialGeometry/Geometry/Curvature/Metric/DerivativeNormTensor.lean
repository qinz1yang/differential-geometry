import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem iteratedCurvatureTensor_eq_iterCov (g : SmoothRiemannianMetric I M)
    (k : ℕ) :
    iteratedCurvatureTensor g k = iterCov g 4 (metricRm04 g) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply DFunLike.ext
    intro x
    change totalNabla0SFun (4 + k) (metricCov g) (iteratedCurvatureTensor g k) x =
      totalNabla0SFun (4 + k) (metricCov g) (iterCov g 4 (metricRm04 g) k) x
    exact congrArg (fun A => totalNabla0SFun (4 + k) (metricCov g) A x) ih

end DifferentialGeometry.Geometry.Curvature
