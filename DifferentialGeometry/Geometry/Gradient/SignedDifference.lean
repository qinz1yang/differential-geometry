import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Geometry.Gradient

theorem abs_mvfderiv_signed_difference_le_gradient_norm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (u v : M → ℝ) (σ : ℝ)
    (x : M) (z : TangentSpace I x) :
    |mvfderiv I u x z - σ * mvfderiv I v x z| ≤
      Real.sqrt (g.inner x (gradFun g u x - σ • gradFun g v x)
        (gradFun g u x - σ • gradFun g v x)) * Real.sqrt (g.inner x z z) := by
  have h := abs_metric_inner_le_sqrt_metric_quadratic g x
    (gradFun g u x - σ • gradFun g v x) z
  have he : g.inner x (gradFun g u x - σ • gradFun g v x) z =
      mvfderiv I u x z - σ * mvfderiv I v x z := by
    rw [map_sub, sub_apply, map_smul, smul_apply, inner_gradFun, inner_gradFun]
    rfl
  rwa [he] at h

end DifferentialGeometry.Geometry.Gradient
