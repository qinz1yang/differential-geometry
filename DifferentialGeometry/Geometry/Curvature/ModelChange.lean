import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.ModelChange

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricScalarAt_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (x : M) :
    metricScalarAt (g.transContinuousLinearEquiv e) x = metricScalarAt g x := by
  change metricScalarAt (Diffeomorph.pullbackMetricCross g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm) x = _
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact metricScalarAt_localPull g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm.isLocalDiffeomorph x

end

end DifferentialGeometry.Geometry.Curvature
