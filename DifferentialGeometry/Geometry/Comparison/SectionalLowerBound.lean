import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem gInner_sq_le_mul (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  exact SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g x v w

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem SectionalBoundedBelowAt.mono {g : SmoothRiemannianMetric I M} {x : M}
    {K K' : ℝ} (h : SectionalBoundedBelowAt g x K') (hKK' : K ≤ K') :
    SectionalBoundedBelowAt g x K := by
  intro v w
  have hG := gInner_sq_le_mul g x v w
  exact (mul_le_mul_of_nonneg_right hKK' (sub_nonneg.mpr hG)).trans (h v w)

end DifferentialGeometry.Geometry.Riemannian
