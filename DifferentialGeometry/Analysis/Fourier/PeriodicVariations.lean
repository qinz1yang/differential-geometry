import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory
open scoped ComplexConjugate NNReal

namespace DifferentialGeometry.Analysis

private theorem hasDerivAt_sin_div_frequency {m : ℕ} (hm : 0 < m) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Real.sin (2 * Real.pi * m * r) / (2 * Real.pi * m))
      (Real.cos (2 * Real.pi * m * s)) s := by
  have hfreq : 2 * Real.pi * (m : ℝ) ≠ 0 := by positivity
  simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ hfreq] using
    (((hasDerivAt_id s).const_mul (2 * Real.pi * m)).sin).div_const (2 * Real.pi * m)

private theorem hasDerivAt_neg_cos_div_frequency {m : ℕ} (hm : 0 < m) (s : ℝ) :
    HasDerivAt (fun r : ℝ => -Real.cos (2 * Real.pi * m * r) / (2 * Real.pi * m))
      (Real.sin (2 * Real.pi * m * s)) s := by
  have hfreq : 2 * Real.pi * (m : ℝ) ≠ 0 := by positivity
  simpa only [id_eq, Pi.neg_apply, mul_one, neg_mul, neg_neg, mul_div_cancel_right₀ _ hfreq] using
    ((((hasDerivAt_id s).const_mul (2 * Real.pi * m)).cos).neg).div_const
      (2 * Real.pi * m)

private theorem periodic_sin_div_frequency (m : ℕ) :
    Function.Periodic
      (fun s : ℝ => Real.sin (2 * Real.pi * m * s) / (2 * Real.pi * m)) 1 := by
  intro s
  dsimp only
  rw [show 2 * Real.pi * (m : ℝ) * (s + 1) =
    2 * Real.pi * m * s + m * (2 * Real.pi) by ring, Real.sin_add_nat_mul_two_pi]

private theorem periodic_neg_cos_div_frequency (m : ℕ) :
    Function.Periodic
      (fun s : ℝ => -Real.cos (2 * Real.pi * m * s) / (2 * Real.pi * m)) 1 := by
  intro s
  dsimp only
  rw [show 2 * Real.pi * (m : ℝ) * (s + 1) =
    2 * Real.pi * m * s + m * (2 * Real.pi) by ring, Real.cos_add_nat_mul_two_pi]

private theorem lipschitzWith_sin_div_frequency {m : ℕ} (hm : 0 < m) :
    LipschitzWith 1
      (fun s : ℝ => Real.sin (2 * Real.pi * m * s) / (2 * Real.pi * m)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s => (hasDerivAt_sin_div_frequency hm s).differentiableAt)
  intro s
  rw [(hasDerivAt_sin_div_frequency hm s).deriv]
  exact_mod_cast Real.abs_cos_le_one (2 * Real.pi * m * s)

private theorem lipschitzWith_neg_cos_div_frequency {m : ℕ} (hm : 0 < m) :
    LipschitzWith 1
      (fun s : ℝ => -Real.cos (2 * Real.pi * m * s) / (2 * Real.pi * m)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s => (hasDerivAt_neg_cos_div_frequency hm s).differentiableAt)
  intro s
  rw [(hasDerivAt_neg_cos_div_frequency hm s).deriv]
  exact_mod_cast Real.abs_sin_le_one (2 * Real.pi * m * s)

private theorem conj_exp_mul_I_pow (θ : ℝ) (m : ℕ) :
    conj (Complex.exp ((θ : ℂ) * Complex.I)) ^ m =
      (Real.cos ((m : ℝ) * θ) : ℂ) - (Real.sin ((m : ℝ) * θ) : ℂ) * Complex.I := by
  rw [← map_pow, ← Complex.exp_nat_mul]
  have he : (m : ℂ) * ((θ : ℂ) * Complex.I) = ((m * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem integral_fourier_eq_zero_of_periodic_variations
    {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (θ : P → ℝ) (hθ : AEMeasurable θ μ) {F : P → ℝ} (hF : Integrable F μ)
    (hvariation : ∀ ψ : ℝ → ℝ, Differentiable ℝ ψ →
      (∃ C : ℝ≥0, LipschitzWith C ψ) → Function.Periodic ψ 1 →
      (∫ p, deriv ψ (θ p / (2 * Real.pi)) * F p ∂μ) = 0)
    {m : ℕ} (hm : 0 < m) :
    (∫ p, (F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m ∂μ) = 0 := by
  have hcos := hvariation
    (fun s : ℝ => Real.sin (2 * Real.pi * m * s) / (2 * Real.pi * m))
    (fun s => (hasDerivAt_sin_div_frequency hm s).differentiableAt)
    ⟨1, lipschitzWith_sin_div_frequency hm⟩ (periodic_sin_div_frequency m)
  have hsin := hvariation
    (fun s : ℝ => -Real.cos (2 * Real.pi * m * s) / (2 * Real.pi * m))
    (fun s => (hasDerivAt_neg_cos_div_frequency hm s).differentiableAt)
    ⟨1, lipschitzWith_neg_cos_div_frequency hm⟩ (periodic_neg_cos_div_frequency m)
  have harg (r : ℝ) : 2 * Real.pi * (m : ℝ) * (r / (2 * Real.pi)) = m * r := by
    field_simp
  simp only [(hasDerivAt_sin_div_frequency hm _).deriv, harg] at hcos
  simp only [(hasDerivAt_neg_cos_div_frequency hm _).deriv, harg] at hsin
  have hem : AEStronglyMeasurable
      (fun p => conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m) μ := by
    have he := (Complex.continuous_exp.measurable.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hθ).mul_const Complex.I)).aestronglyMeasurable
    exact (Complex.continuous_conj.comp_aestronglyMeasurable he).pow m
  have he_bound : ∀ᵐ p ∂μ, ‖conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    simp only [norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, one_pow, le_refl]
  have hi := hF.ofReal.mul_bdd hem he_bound
  apply Complex.ext
  · change (∫ p, (F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m ∂μ).re = 0
    have hre := integral_re hi
    change (∫ p, ((F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m).re ∂μ) =
      (∫ p, (F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m ∂μ).re at hre
    rw [← hre]
    calc
      _ = ∫ p, Real.cos (m * θ p) * F p ∂μ := by
        apply integral_congr_ae
        filter_upwards with p
        rw [conj_exp_mul_I_pow]
        simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          mul_one, sub_zero]
        ring
      _ = 0 := hcos
  · change (∫ p, (F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m ∂μ).im = 0
    have him := integral_im hi
    change (∫ p, ((F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m).im ∂μ) =
      (∫ p, (F p : ℂ) * conj (Complex.exp ((θ p : ℂ) * Complex.I)) ^ m ∂μ).im at him
    rw [← him]
    calc
      _ = ∫ p, -(Real.sin (m * θ p) * F p) ∂μ := by
        apply integral_congr_ae
        filter_upwards with p
        rw [conj_exp_mul_I_pow]
        simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          mul_one, zero_sub]
        ring
      _ = 0 := by rw [integral_neg, hsin, neg_zero]

private theorem integrable_radial_real_part
    {h : ℂ → ℂ} (hh : IntegrableOn h (Metric.ball 0 1)) :
    IntegrableOn (fun z => (h z * Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2).re)
      (Metric.ball 0 1) := by
  have hem : AEStronglyMeasurable
      (fun z : ℂ => Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2)
        (volume.restrict (Metric.ball 0 1)) :=
    ((Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp Complex.measurable_arg).mul_const Complex.I)).pow_const 2).aestronglyMeasurable
  have he_bound : ∀ᵐ z : ℂ ∂(volume.restrict (Metric.ball 0 1)),
      ‖Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards with z
    simp only [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, le_refl]
  exact (hh.mul_bdd hem he_bound).re

theorem integrable_radial_fourier_moment
    {h : ℂ → ℂ} (hh : IntegrableOn h (Metric.ball 0 1)) (m : ℕ) :
    IntegrableOn (fun z =>
      ((h z * Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2).re : ℂ) *
        conj (Complex.exp ((z.arg : ℂ) * Complex.I)) ^ m) (Metric.ball 0 1) := by
  have he : AEStronglyMeasurable
      (fun z : ℂ => Complex.exp ((z.arg : ℂ) * Complex.I))
        (volume.restrict (Metric.ball 0 1)) :=
    (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp Complex.measurable_arg).mul_const Complex.I)).aestronglyMeasurable
  have hem := (Complex.continuous_conj.comp_aestronglyMeasurable he).pow m
  have he_bound : ∀ᵐ z : ℂ ∂(volume.restrict (Metric.ball 0 1)),
      ‖conj (Complex.exp ((z.arg : ℂ) * Complex.I)) ^ m‖ ≤ (1 : ℝ) := by
    filter_upwards with z
    simp only [norm_pow, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, one_pow, le_refl]
  exact (integrable_radial_real_part hh).ofReal.mul_bdd hem he_bound

theorem integral_radial_fourier_eq_zero_of_periodic_variations
    {h : ℂ → ℂ} (hh : IntegrableOn h (Metric.ball 0 1))
    (hvariation : ∀ ψ : ℝ → ℝ, Differentiable ℝ ψ →
      (∃ C : ℝ≥0, LipschitzWith C ψ) → Function.Periodic ψ 1 →
      (∫ z in Metric.ball 0 1, deriv ψ (z.arg / (2 * Real.pi)) *
        (h z * Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2).re) = 0)
    (n : ℕ) :
    (∫ z in Metric.ball 0 1,
      ((h z * Complex.exp ((z.arg : ℂ) * Complex.I) ^ 2).re : ℂ) *
        conj (Complex.exp ((z.arg : ℂ) * Complex.I)) ^ (n + 2)) = 0 := by
  exact integral_fourier_eq_zero_of_periodic_variations Complex.arg
    Complex.measurable_arg.aemeasurable (integrable_radial_real_part hh) hvariation (by positivity)

end DifferentialGeometry.Analysis

end
