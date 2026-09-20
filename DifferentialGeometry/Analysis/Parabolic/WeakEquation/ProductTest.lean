import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradientFun_const_mul_field
    (g : SmoothRiemannianMetric I M) (c : ℝ) (f : M → ℝ) (x : M) :
    gradientFun g (fun y => c * f y) x = c • gradientFun g f x := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul, gradientFun_const, zero_smul]
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · exact gradientFun_const_smul g c hf
  · have hcf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => c * f y) x := by
      intro hcf
      have hback := hcf.const_smul c⁻¹
      have hfun : c⁻¹ • (fun y => c * f y) = f := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [hfun] at hback
      exact hf hback
    have hfzero : gradientFun g f x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero g f (mfderiv_zero_of_not_mdifferentiableAt hf)
    have hcfzero : gradientFun g (fun y => c * f y) x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero g (fun y => c * f y)
        (mfderiv_zero_of_not_mdifferentiableAt hcf)
    rw [hcfzero, hfzero, smul_zero]

private theorem parabolic_test_residual_prod
    (g : SmoothRiemannianMetric I M) (w : ℝ) (t : ℝ) (x : M)
    (X : TangentSpace I x) (η : ℝ → ℝ) (χ : M → ℝ) :
    w * (deriv (fun s => η s * χ x) t +
      g.inner x X (gradientFun g (fun y => η t * χ y) x)) =
      deriv η t * (χ x * w) + η t * (w * g.inner x X (gradientFun g χ x)) := by
  rw [deriv_mul_const_field, gradientFun_const_mul_field,
    (g.inner x X).map_smul, smul_eq_mul]
  ring

variable [MeasurableSpace M]

theorem integrable_and_integral_integral_parabolic_test_residual_prod
    (μ : Measure ℝ) (ν : ℝ → Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    (η : ℝ → ℝ) (χ : M → ℝ)
    (hmassSpatial : ∀ᵐ t ∂μ,
      Integrable (fun x => deriv η t * (χ x * w (t, x))) (ν t))
    (hfluxSpatial : ∀ᵐ t ∂μ,
      Integrable (fun x => η t *
        (w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x))) (ν t))
    (hmassTime : Integrable (fun t => deriv η t * (∫ x, χ x * w (t, x) ∂ν t)) μ)
    (hfluxTime : Integrable (fun t => η t *
      (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t)) μ) :
    let R := fun (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => η s * χ x) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => η t * χ y) x))
    (∀ᵐ t ∂μ, Integrable (R t) (ν t)) ∧
      Integrable (fun t => ∫ x, R t x ∂ν t) μ ∧
      (∫ t, ∫ x, R t x ∂ν t ∂μ) =
        (∫ t, deriv η t * (∫ x, χ x * w (t, x) ∂ν t) ∂μ) +
          ∫ t, η t *
            (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t) ∂μ := by
  intro R
  have hpoint (t : ℝ) (x : M) : R t x =
      deriv η t * (χ x * w (t, x)) + η t *
        (w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x)) :=
    parabolic_test_residual_prod (g t) (w (t, x)) t x (X t x) η χ
  have hint : ∀ᵐ t ∂μ, (∫ x, R t x ∂ν t) =
      deriv η t * (∫ x, χ x * w (t, x) ∂ν t) + η t *
        (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t) := by
    filter_upwards [hmassSpatial, hfluxSpatial] with t htMass htFlux
    rw [integral_congr_ae (ae_of_all (ν t) (hpoint t)), integral_add htMass htFlux,
      integral_const_mul, integral_const_mul]
  refine ⟨?_, (hmassTime.add hfluxTime).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [hmassSpatial, hfluxSpatial] with t htMass htFlux
    exact (htMass.add htFlux).congr (ae_of_all (ν t) fun x => (hpoint t x).symm)
  · rw [integral_congr_ae hint, integral_add hmassTime hfluxTime]

end DifferentialGeometry.Geometry.Operator
