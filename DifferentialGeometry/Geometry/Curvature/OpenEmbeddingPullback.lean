import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Curvature.ScalarPullback

set_option autoImplicit false
noncomputable section
open Function DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold J N]

theorem metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc g) f hf hinj) x =
      metricScalarAt g (f x) / c := by
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart g f hf hinj c hc
    hf.image (diffeomorphOntoImage f hf hinj) (diffeomorphOntoImage_apply f hf hinj)]
  rw [metricScalarAt_pullback_scaleMetric_restrictOpenCross, diffeomorphOntoImage_apply]

end DifferentialGeometry.Geometry.Curvature
