import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance scalingComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance scalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metricCovDerivStep_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) (a + 2)) :
    metricCovDerivStep (scaleMetric c hc g) a A = metricCovDerivStep g a A := by
  apply DFunLike.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply, lcConn_scaleMetric]

theorem tensor02CovDeriv_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (scaleMetric c hc g) a = tensor02CovDeriv A g a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change metricCovDerivStep (scaleMetric c hc g) a
      (tensor02CovDeriv A (scaleMetric c hc g) a) =
      metricCovDerivStep g a (tensor02CovDeriv A g a)
    rw [ih, metricCovDerivStep_scaleMetric]

theorem tensor02CovDerivNormWith_smul (gcov gnorm : SmoothRiemannianMetric I M)
    (c : ℝ) (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a (c • A) gcov gnorm x =
      |c| * tensor02CovDerivNormWith a A gcov gnorm x := by
  simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  exact sqrt_normSq0S_smul gnorm x (a + 2) c _

theorem tensor02CovDerivNormWith_scaleMetric (gcov gnorm : SmoothRiemannianMetric I M)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a A (scaleMetric c hc gcov) (scaleMetric d hd gnorm) x =
      (Real.sqrt d)⁻¹ ^ (a + 2) * tensor02CovDerivNormWith a A gcov gnorm x := by
  unfold tensor02CovDerivNormWith
  rw [tensor02CovDeriv_scaleMetric, normSq0S_scale,
    Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hd.le) _)]
  congr 1
  have heq : d⁻¹ = ((Real.sqrt d)⁻¹) ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  rw [heq, pow_right_comm, Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg d)) _)]

end DifferentialGeometry.CheegerGromovCompactness
