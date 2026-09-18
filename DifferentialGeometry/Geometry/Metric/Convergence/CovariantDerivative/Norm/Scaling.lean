import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem tensor02CovDeriv_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I N)
    (A : Tensor0SField (I := I) (M := N) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (scaleMetric c hc g) a = tensor02CovDeriv A g a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change metricCovDerivStep (scaleMetric c hc g) a
      (tensor02CovDeriv A (scaleMetric c hc g) a) = _
    rw [ih]
    apply DFunLike.ext
    intro y
    rw [metricCovDerivStep_apply]
    change totalNabla0SFun (a + 2) (LeviCivita (scaleMetric c hc g)) _ y = _
    have hconn : LeviCivita (scaleMetric c hc g) = LeviCivita g := lcConn_scaleMetric c hc g
    rw [hconn]
    rfl

theorem tensor02CovDerivNormWith_smul_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I N)
    (A : Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (w : ℝ) (a : ℕ) (y : N) :
    tensor02CovDerivNormWith a (w • A) (scaleMetric c hc g) (scaleMetric c hc g) y =
      (Real.sqrt ((c⁻¹) ^ (a + 2)) * |w|) * tensor02CovDerivNormWith a A g g y := by
  unfold tensor02CovDerivNormWith
  rw [tensor02CovDeriv_scaleMetric, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_smul]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [normSq0S_scale, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hc.le) _),
    sqrt_normSq0S_smul, ← mul_assoc, ← tensor02_cov_deriv_eq_cov_deriv_of_field]


end DifferentialGeometry.CheegerGromovCompactness
