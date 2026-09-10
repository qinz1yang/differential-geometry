import DifferentialGeometry.Geometry.Curvature.MetricScaling
import DifferentialGeometry.Geometry.Metric.SharpScaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

theorem ricciSharp_scaleMetric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    (v : TangentSpace I x) :
    ricciSharp (scaleMetric c hc g) x v = c⁻¹ • ricciSharp g x v := by
  rw [ricciSharp_apply, ricciSharpVec, ricciTensor_scaleMetric, metricSharp_scaleMetric]
  rfl

end Poincare.Geometry.Curvature
