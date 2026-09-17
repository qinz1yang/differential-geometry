import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem square_le_sum_of_sqrt_bound {d L₁ L₂ : ℝ}
    (hd : 0 ≤ d) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (h : d ≤ 16 + 48 * (Real.sqrt L₁ + Real.sqrt L₂)) :
    collapsedVolumeChi * d ^ 2 - 1 ≤ L₁ + L₂ := by
  have hsq₁ := Real.sq_sqrt hL₁
  have hsq₂ := Real.sq_sqrt hL₂
  have hroots : 0 ≤ Real.sqrt L₁ + Real.sqrt L₂ := by positivity
  have hsum : (Real.sqrt L₁ + Real.sqrt L₂) ^ 2 ≤ 2 * (L₁ + L₂) := by
    nlinarith only [hsq₁, hsq₂, sq_nonneg (Real.sqrt L₁ - Real.sqrt L₂)]
  have hupper : d ^ 2 ≤ (16 + 48 * (Real.sqrt L₁ + Real.sqrt L₂)) ^ 2 :=
    pow_le_pow_left₀ hd h 2
  norm_num [collapsedVolumeChi]
  nlinarith only [hupper, hsum, sq_nonneg (24 * (Real.sqrt L₁ + Real.sqrt L₂) - 16)]

theorem two_point_coercivity_of_upper_dini_bound
    {d : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hcont : ContinuousOn d (Icc 0 1))
    (hac : ∀ c ∈ Ioc (0 : ℝ) 1, AbsolutelyContinuousOnInterval d c 1)
    (hzero : d 0 = 0) (hnonneg : 0 ≤ d 1)
    (hdini : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
      slope d t s ≤
        8 * t ^ (-(1 / 2) : ℝ) +
          (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)) *
            t ^ (-(3 / 4) : ℝ) + ε) :
    collapsedVolumeChi * (d 1) ^ 2 - 1 ≤ L₁ + L₂ := by
  have hhalf : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 1 :=
    intervalIntegrable_rpow' (by norm_num)
  have hquarter : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 4) : ℝ)) volume 0 1 :=
    intervalIntegrable_rpow' (by norm_num)
  have hG := (hhalf.const_mul 8).add
    (hquarter.const_mul (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)))
  have hint := hcont.sub_le_integral_of_dini_le (by norm_num : (0 : ℝ) ≤ 1)
    hac hG hdini
  have hh : (∫ t in (0 : ℝ)..1, t ^ (-(1 / 2) : ℝ)) = 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num
  have hq : (∫ t in (0 : ℝ)..1, t ^ (-(3 / 4) : ℝ)) = 4 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4)))]
    norm_num
  rw [hzero, sub_zero, integral_add (hhalf.const_mul 8)
      (hquarter.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hh, hq] at hint
  apply square_le_sum_of_sqrt_bound hnonneg hL₁ hL₂
  have h3 : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hprod := mul_le_mul_of_nonneg_right h3
    (add_nonneg (Real.sqrt_nonneg L₁) (Real.sqrt_nonneg L₂))
  nlinarith only [hint, hprod, Real.sqrt_nonneg L₁, Real.sqrt_nonneg L₂]

theorem two_point_coercivity_of_upper_dini_bound_interval
    {d : ℝ → ℝ} {L₁ L₂ tau : ℝ} (htau : 0 < tau)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hcont : ContinuousOn d (Icc 0 tau))
    (hac : ∀ c ∈ Ioc (0 : ℝ) tau, AbsolutelyContinuousOnInterval d c tau)
    (hzero : d 0 = 0) (hnonneg : 0 ≤ d tau)
    (hdini : ∀ t ∈ Ioo (0 : ℝ) tau, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
      slope d t s ≤
        8 * t ^ (-(1 / 2) : ℝ) +
          (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)) *
            tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) + ε) :
    collapsedVolumeChi * (d tau) ^ 2 / tau - 1 ≤ L₁ + L₂ := by
  have hhalf : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hquarter : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 4) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hG := (hhalf.const_mul 8).add
    (hquarter.const_mul ((8 * Real.sqrt L₂ + Real.sqrt 3 *
      (Real.sqrt L₁ + Real.sqrt L₂)) * tau ^ ((1 / 4) : ℝ)))
  have hint := hcont.sub_le_integral_of_dini_le htau.le hac hG hdini
  have hh : (∫ t in (0 : ℝ)..tau, t ^ (-(1 / 2) : ℝ)) = 2 * Real.sqrt tau := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num
    rw [Real.sqrt_eq_rpow]
    ring
  have hq : (∫ t in (0 : ℝ)..tau, t ^ (-(3 / 4) : ℝ)) =
      4 * tau ^ ((1 / 4) : ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4)))]
    norm_num
    ring
  rw [hzero, sub_zero, integral_add (hhalf.const_mul 8)
      (hquarter.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hh, hq] at hint
  have hpow : tau ^ ((1 / 4) : ℝ) * tau ^ ((1 / 4) : ℝ) = Real.sqrt tau := by
    rw [← Real.rpow_add htau]
    norm_num
    exact (Real.sqrt_eq_rpow tau).symm
  have hprod : (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)) *
        tau ^ ((1 / 4) : ℝ) * (4 * tau ^ ((1 / 4) : ℝ)) =
      4 * (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)) *
        Real.sqrt tau := by
    rw [← hpow]
    ring
  rw [hprod] at hint
  have h3 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcoeff := mul_le_mul_of_nonneg_right h3
    (add_nonneg (Real.sqrt_nonneg L₁) (Real.sqrt_nonneg L₂))
  have hbound : d tau / Real.sqrt tau ≤ 16 + 48 * (Real.sqrt L₁ + Real.sqrt L₂) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr htau)).mpr
    have hc : 4 * (8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂)) ≤
        48 * (Real.sqrt L₁ + Real.sqrt L₂) := by
      nlinarith only [hcoeff, Real.sqrt_nonneg L₁, Real.sqrt_nonneg L₂]
    have hc' := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg tau)
    nlinarith only [hint, hc']
  have hout := square_le_sum_of_sqrt_bound
    (div_nonneg hnonneg (Real.sqrt_nonneg tau)) hL₁ hL₂ hbound
  rwa [div_pow, Real.sq_sqrt htau.le, ← mul_div_assoc] at hout

theorem two_point_coercivity_of_upper_dini_sum_bound_interval
    {d : ℝ → ℝ} {L₁ L₂ tau : ℝ} (htau : 0 < tau)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hcont : ContinuousOn d (Icc 0 tau))
    (hac : ∀ c ∈ Ioc (0 : ℝ) tau, AbsolutelyContinuousOnInterval d c tau)
    (hzero : d 0 = 0) (hnonneg : 0 ≤ d tau)
    (hdini : ∀ t ∈ Ioo (0 : ℝ) tau, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
      slope d t s ≤
        8 * t ^ (-(1 / 2) : ℝ) +
          ((8 + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂)) *
            tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) + ε) :
    collapsedVolumeChi * (d tau) ^ 2 / tau - 1 ≤ L₁ + L₂ := by
  have hhalf : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hquarter : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 4) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hG := (hhalf.const_mul 8).add
    (hquarter.const_mul (((8 + Real.sqrt 3) *
      (Real.sqrt L₁ + Real.sqrt L₂)) * tau ^ ((1 / 4) : ℝ)))
  have hint := hcont.sub_le_integral_of_dini_le htau.le hac hG hdini
  have hh : (∫ t in (0 : ℝ)..tau, t ^ (-(1 / 2) : ℝ)) = 2 * Real.sqrt tau := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num
    rw [Real.sqrt_eq_rpow]
    ring
  have hq : (∫ t in (0 : ℝ)..tau, t ^ (-(3 / 4) : ℝ)) =
      4 * tau ^ ((1 / 4) : ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4)))]
    norm_num
    ring
  rw [hzero, sub_zero, integral_add (hhalf.const_mul 8)
      (hquarter.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hh, hq] at hint
  have hpow : tau ^ ((1 / 4) : ℝ) * tau ^ ((1 / 4) : ℝ) = Real.sqrt tau := by
    rw [← Real.rpow_add htau]
    norm_num
    exact (Real.sqrt_eq_rpow tau).symm
  have hprod : ((8 + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂)) *
        tau ^ ((1 / 4) : ℝ) * (4 * tau ^ ((1 / 4) : ℝ)) =
      4 * ((8 + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂)) *
        Real.sqrt tau := by
    rw [← hpow]
    ring
  rw [hprod] at hint
  have h3 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hcoeff := mul_le_mul_of_nonneg_right h3
    (add_nonneg (Real.sqrt_nonneg L₁) (Real.sqrt_nonneg L₂))
  have hbound : d tau / Real.sqrt tau ≤ 16 + 48 * (Real.sqrt L₁ + Real.sqrt L₂) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr htau)).mpr
    have hc : 4 * ((8 + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂)) ≤
        48 * (Real.sqrt L₁ + Real.sqrt L₂) := by
      nlinarith only [hcoeff, Real.sqrt_nonneg L₁, Real.sqrt_nonneg L₂]
    have hc' := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg tau)
    nlinarith only [hint, hc']
  have hout := square_le_sum_of_sqrt_bound
    (div_nonneg hnonneg (Real.sqrt_nonneg tau)) hL₁ hL₂ hbound
  rwa [div_pow, Real.sq_sqrt htau.le, ← mul_div_assoc] at hout

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
