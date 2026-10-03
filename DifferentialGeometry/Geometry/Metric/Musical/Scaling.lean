import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Operator.Gradient.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Metric

theorem metricSharp_scaleMetric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (scaleMetric c hc g) x α = c⁻¹ • metricSharp g x α := by
  apply (metricFlatMap (scaleMetric c hc g) x).injective
  ext v
  rw [metricFlatMap_apply, metricFlatMap_apply, inner_metricSharp, scaleMetric_inner,
    map_smul (g.inner x), smul_apply, inner_metricSharp]
  change α v = c * (c⁻¹ * α v)
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end DifferentialGeometry.Geometry.Metric
