import DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Curvature.OperatorNaturality

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
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

theorem curvature_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) (x : M) :
    metricScalarAt g x = metricScalarAt h (f x) ∧
      leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) =
        leastCurvatureOperatorEigenvalueAt h (f x) (metricAlgebraicCurvatureTensorAt h (f x)) := by
  have he : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric q v w
  have hone : scaleMetric 1 zero_lt_one h = h := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [scaleMetric_inner, one_mul]
  constructor
  · have hr := metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale h f hf hinj 1 zero_lt_one x
    simpa only [hone, div_one, ← he] using hr
  · rw [he]
    exact leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj x
end DifferentialGeometry.Geometry.Curvature
