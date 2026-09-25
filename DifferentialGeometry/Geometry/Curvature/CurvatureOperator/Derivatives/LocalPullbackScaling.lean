import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem curvDerivNormSq_localPullMetric
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (j : ℕ) (z : M) :
    curvDerivNormSq j (localPullMetric g f hf) z = curvDerivNormSq j g (f z) := by
  have heq := congrArg (fun t : ℝ => t ^ 2)
    (curvDerivNorm_localPullMetric g f hf j z)
  simpa only [curvDerivNorm, curvDerivNormSq,
    Real.sq_sqrt (Tensor0SBundle.normSq0S_nonneg _ _ _ _)] using heq

theorem curvDerivNormSq_eq_of_scaled_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {q : ℝ} (hq : 0 < q)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = q * h.inner (f y) (mfderiv I J f y v) (mfderiv I J f y w))
    (j : ℕ) (z : M) :
    curvDerivNormSq j h (f z) = q ^ (j + 2) * curvDerivNormSq j g z := by
  have hg : g = localPullMetric (scaleMetric q hq h) f hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact hmetric y v w
  rw [hg, curvDerivNormSq_localPullMetric, curvDerivNormSq_scaleMetric,
    ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne', one_pow, one_mul]

theorem curvDerivNormSq_le_of_scaled_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {q : ℝ} (hq : 0 < q)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = q * h.inner (f y) (mfderiv I J f y v) (mfderiv I J f y w))
    {z : M} {x : N} (hpoint : f z = x) {j : ℕ} {B : ℝ}
    (hbound : curvDerivNormSq j g z ≤ B) :
    curvDerivNormSq j h x ≤ q ^ (j + 2) * B := by
  rw [← hpoint, curvDerivNormSq_eq_of_scaled_local_isometry g h f hf hq hmetric]
  exact mul_le_mul_of_nonneg_left hbound (pow_nonneg hq.le _)

end DifferentialGeometry.CheegerGromovCompactness
