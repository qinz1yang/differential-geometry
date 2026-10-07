import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.BilinearFormBounds
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem scaled_pullback_inner_bounds_of_tensor0SFiberNorm_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (c : ℝ) (hc : 0 < c) (x : M) {ε : ℝ}
    (herror : tensor0SFiberNorm g x 2
      (((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap.comp
        (c • localPullInner h f x - g.inner x)).uncurryLeft) ≤ ε)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤
        (scaleMetric c hc h).inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ∧
      (scaleMetric c hc h).inner (f x) (mfderiv I J f x v) (mfderiv I J f x v) ≤
        (1 + ε) * g.inner x v v := by
  simpa only [smul_apply, smul_eq_mul, localPullInner_apply,
    scaleMetric_inner] using
    bilinear_apply_bounds_of_tensor0SFiberNorm_sub_le g x (c • localPullInner h f x) herror v

end DifferentialGeometry
