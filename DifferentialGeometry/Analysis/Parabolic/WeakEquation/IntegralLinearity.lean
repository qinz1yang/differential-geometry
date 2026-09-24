import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open MeasureTheory
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [MeasurableSpace M]

omit [MeasurableSpace M] in
private theorem time_spatial_derivative_add
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    {f h : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hft : DifferentiableAt ℝ (fun s => f (s, x)) t)
    (hht : DifferentiableAt ℝ (fun s => h (s, x)) t)
    (hfx : MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (hhx : MDifferentiableAt I 𝓘(ℝ) (fun y => h (t, y)) x) :
    w (t, x) * deriv (fun s => f (s, x) + h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y) + h (t, y)) x) =
    (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) +
    (w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x)) := by
  rw [deriv_fun_add hft hht, mvfderiv_fun_add hfx hhx, map_add]
  ring

omit [MeasurableSpace M] in
private theorem mvfderiv_const_mul_field (c : ℝ) (f : M → ℝ) (x : M) :
    mvfderiv I (fun y => c * f y) x = c • mvfderiv I f x := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul, mvfderiv_const, zero_smul]
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · simpa only [smul_eq_mul, mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] using
      mvfderiv_fun_smul (mdifferentiableAt_const (c := c)) hf
  · have hcf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => c * f y) x := by
      intro hcf
      have hback := hcf.const_smul c⁻¹
      apply hf
      have hfun : c⁻¹ • (fun y => c * f y) = f := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [hfun] at hback
      exact hback
    have hfzero : mvfderiv I f x = 0 := by
      simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
        ContinuousLinearMap.comp_zero]
    have hcfzero : mvfderiv I (fun y => c * f y) x = 0 := by
      simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hcf,
        ContinuousLinearMap.comp_zero]
    rw [hcfzero, hfzero, smul_zero]


omit [MeasurableSpace M] in
private theorem time_spatial_derivative_const_mul
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (c : ℝ) (f : ℝ × M → ℝ) (t : ℝ) (x : M) :
    w (t, x) * deriv (fun s => c * f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => c * f (t, y)) x) =
    c * (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) := by
  rw [deriv_const_mul_field, mvfderiv_const_mul_field, map_smul, smul_eq_mul]
  ring

theorem integrable_and_integral_integral_time_spatial_derivative_add
    (μ : Measure ℝ) (ν : ℝ → Measure M)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    {f h : ℝ × M → ℝ}
    (hft : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => f (s, x)) t)
    (hht : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => h (s, x)) t)
    (hfx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (hhx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, MDifferentiableAt I 𝓘(ℝ) (fun y => h (t, y)) x)
    (hfint : ∀ᵐ t ∂μ, Integrable (fun x => w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) (ν t))
    (hhint : ∀ᵐ t ∂μ, Integrable (fun x => w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x)) (ν t))
    (hftime : Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) μ)
    (hhtime : Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) =>
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x)
    (∀ᵐ t ∂μ, Integrable (R (f + h) t) (ν t)) ∧
      Integrable (fun t => ∫ x, R (f + h) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (f + h) t x ∂ν t ∂μ) =
        (∫ t, ∫ x, R f t x ∂ν t ∂μ) + ∫ t, ∫ x, R h t x ∂ν t ∂μ := by
  dsimp only
  have heq : ∀ᵐ t ∂μ, (fun x => w (t, x) * deriv (fun s => (f + h) (s, x)) t +
      A (t, x) (mvfderiv I (fun y => (f + h) (t, y)) x)) =ᵐ[ν t]
    (fun x => (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) +
      (w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x))) := by
    filter_upwards [hft, hht, hfx, hhx] with t hftt hhtt hfxt hhxt
    filter_upwards [hftt, hhtt, hfxt, hhxt] with x hftx hhtx hfxx hhxx
    exact time_spatial_derivative_add w A hftx hhtx hfxx hhxx
  have hint : ∀ᵐ t ∂μ,
      (∫ x, w (t, x) * deriv (fun s => (f + h) (s, x)) t +
        A (t, x) (mvfderiv I (fun y => (f + h) (t, y)) x) ∂ν t) =
      (∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) +
      ∫ x, w (t, x) * deriv (fun s => h (s, x)) t +
        A (t, x) (mvfderiv I (fun y => h (t, y)) x) ∂ν t := by
    filter_upwards [heq, hfint, hhint] with t ht hfi hhi
    rw [integral_congr_ae ht, integral_add hfi hhi]
  refine ⟨?_, (hftime.add hhtime).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [heq, hfint, hhint] with t ht hfi hhi
    exact (hfi.add hhi).congr ht.symm
  · rw [integral_congr_ae hint, integral_add hftime hhtime]

theorem integrable_and_integral_integral_time_spatial_derivative_const_mul
    (μ : Measure ℝ) (ν : ℝ → Measure M)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (c : ℝ) {f : ℝ × M → ℝ}
    (hfint : ∀ᵐ t ∂μ, Integrable (fun x => w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) (ν t))
    (hftime : Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) =>
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x)
    (∀ᵐ t ∂μ, Integrable (R (c • f) t) (ν t)) ∧
      Integrable (fun t => ∫ x, R (c • f) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (c • f) t x ∂ν t ∂μ) =
        c * ∫ t, ∫ x, R f t x ∂ν t ∂μ := by
  dsimp only
  have heq : ∀ᵐ t ∂μ, (fun x => w (t, x) * deriv (fun s => (c • f) (s, x)) t +
      A (t, x) (mvfderiv I (fun y => (c • f) (t, y)) x)) =ᵐ[ν t]
    (fun x => c * (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x))) := by
    exact ae_of_all μ fun t => ae_of_all (ν t) fun x =>
      time_spatial_derivative_const_mul w A c f t x
  have hint : ∀ᵐ t ∂μ,
      (∫ x, w (t, x) * deriv (fun s => (c • f) (s, x)) t +
        A (t, x) (mvfderiv I (fun y => (c • f) (t, y)) x) ∂ν t) =
      c * ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t := by
    filter_upwards [heq] with t ht
    rw [integral_congr_ae ht, integral_const_mul]
  refine ⟨?_, (hftime.const_mul c).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [heq, hfint] with t ht hfi
    exact (hfi.const_mul c).congr ht.symm
  · rw [integral_congr_ae hint, integral_const_mul]

end DifferentialGeometry.Analysis.Parabolic
