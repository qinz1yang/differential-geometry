import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

noncomputable section
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

private theorem curvCovDerivStep_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (A : Tensor0SField (I := I) (M := M) (n := ∞) (a + 4)) :
    curvCovDerivStep (scaleMetric c hc g) a A = curvCovDerivStep g a A := by
  rw [curvStep_eq_covStep, curvStep_eq_covStep]
  apply DFunLike.ext
  intro x
  rw [covStep_apply, covStep_apply, lcConn_scaleMetric]

theorem curvCovDeriv_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) :
    curvCovDeriv (scaleMetric c hc g) a = c • curvCovDeriv g a := by
  induction a with
  | zero =>
    apply DFunLike.ext
    intro x
    exact metricRm_scale c hc g x
  | succ a ih =>
    rw [curvCovDeriv_succ, curvCovDeriv_succ, ih, curvCovDerivStep_scaleMetric,
      curvStep_eq_covStep, curvStep_eq_covStep, covStep_smul]

theorem curvDerivNormSq_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (x : M) :
    curvDerivNormSq a (scaleMetric c hc g) x = c⁻¹ ^ (a + 2) * curvDerivNormSq a g x := by
  unfold curvDerivNormSq
  rw [curvCovDeriv_scaleMetric]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [normSq0S_scale, normSq0S_smul]
  have hw : c⁻¹ ^ (a + 4) * c ^ 2 = c⁻¹ ^ (a + 2) := by
    rw [show a + 4 = (a + 2) + 2 by omega, pow_add, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hc.ne', one_pow, mul_one]
  rw [← mul_assoc, hw]

theorem curvDerivNorm_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (x : M) :
    curvDerivNorm a (scaleMetric c hc g) x = curvDerivNorm a g x / (c * Real.sqrt c ^ a) := by
  unfold curvDerivNorm
  rw [curvDerivNormSq_scaleMetric, Real.sqrt_mul (by positivity)]
  have hw : Real.sqrt (c⁻¹ ^ (a + 2)) = (c * Real.sqrt c ^ a)⁻¹ := by
    have heq : c⁻¹ = ((Real.sqrt c)⁻¹) ^ 2 := by
      rw [inv_pow, Real.sq_sqrt hc.le]
    rw [heq, pow_right_comm, Real.sqrt_sq (by positivity), pow_add]
    simp only [inv_pow, Real.sq_sqrt hc.le]
    ring
  rw [hw, div_eq_mul_inv, mul_comm]
end DifferentialGeometry.CheegerGromovCompactness
