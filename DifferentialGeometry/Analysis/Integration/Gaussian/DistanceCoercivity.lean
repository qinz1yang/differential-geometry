import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem sq_div_le_of_upper_dini_sqrt_sum_bound
    {d : ℝ → ℝ} {L₁ L₂ tau a b : ℝ} (htau : 0 < tau)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hcont : ContinuousOn d (Icc 0 tau))
    (hac : ∀ c ∈ Ioc (0 : ℝ) tau, AbsolutelyContinuousOnInterval d c tau)
    (hzero : d 0 = 0) (hnonneg : 0 ≤ d tau)
    (hdini : ∀ t ∈ Ioo (0 : ℝ) tau, ∀ ε > 0, ∀ᶠ s in 𝓝[>] t,
      slope d t s ≤
        a * t ^ (-(1 / 2) : ℝ) +
          (b * (Real.sqrt L₁ + Real.sqrt L₂)) *
            tau ^ ((1 / 4) : ℝ) * t ^ (-(3 / 4) : ℝ) + ε) :
    (d tau) ^ 2 / tau ≤ 8 * a ^ 2 + 64 * b ^ 2 * (L₁ + L₂) := by
  have hhalf : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hquarter : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 4) : ℝ)) volume 0 tau :=
    intervalIntegrable_rpow' (by norm_num)
  have hG := (hhalf.const_mul a).add
    (hquarter.const_mul ((b *
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
  rw [hzero, sub_zero, integral_add (hhalf.const_mul a)
      (hquarter.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hh, hq] at hint
  have hpow : tau ^ ((1 / 4) : ℝ) * tau ^ ((1 / 4) : ℝ) = Real.sqrt tau := by
    rw [← Real.rpow_add htau]
    norm_num
    exact (Real.sqrt_eq_rpow tau).symm
  have hprod : (b * (Real.sqrt L₁ + Real.sqrt L₂)) *
        tau ^ ((1 / 4) : ℝ) * (4 * tau ^ ((1 / 4) : ℝ)) =
      4 * (b * (Real.sqrt L₁ + Real.sqrt L₂)) *
        Real.sqrt tau := by
    rw [← hpow]
    ring
  rw [hprod] at hint
  have hbound : d tau / Real.sqrt tau ≤ 2 * a + 4 * b * (Real.sqrt L₁ + Real.sqrt L₂) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr htau)).mpr
    nlinarith only [hint]
  have hsq₁ := Real.sq_sqrt hL₁
  have hsq₂ := Real.sq_sqrt hL₂
  have hsum : (Real.sqrt L₁ + Real.sqrt L₂) ^ 2 ≤ 2 * (L₁ + L₂) := by
    nlinarith only [hsq₁, hsq₂, sq_nonneg (Real.sqrt L₁ - Real.sqrt L₂)]
  have hupper := pow_le_pow_left₀
    (div_nonneg hnonneg (Real.sqrt_nonneg tau)) hbound 2
  rw [div_pow, Real.sq_sqrt htau.le] at hupper
  have hscaled := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) (sq_nonneg b))
  nlinarith only [hupper, hscaled,
    sq_nonneg (2 * a - 4 * b * (Real.sqrt L₁ + Real.sqrt L₂))]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

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
  have hbound := DifferentialGeometry.Analysis.sq_div_le_of_upper_dini_sqrt_sum_bound
    (a := 8) (b := 12) htau hL₁ hL₂ hcont hac hzero hnonneg ?_
  · norm_num [collapsedVolumeChi] at hbound ⊢
    rw [mul_div_assoc]
    linarith
  intro t ht ε hε
  filter_upwards [hdini t ht ε hε] with s hs
  refine hs.trans ?_
  have hcoef : 8 + Real.sqrt 3 ≤ 12 := by
    have : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  gcongr
  exact Real.rpow_nonneg ht.1.le _

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
  apply two_point_coercivity_of_upper_dini_sum_bound_interval htau hL₁ hL₂
    hcont hac hzero hnonneg
  intro t ht ε hε
  filter_upwards [hdini t ht ε hε] with s hs
  refine hs.trans ?_
  have hcoef : 8 * Real.sqrt L₂ + Real.sqrt 3 * (Real.sqrt L₁ + Real.sqrt L₂) ≤
      (8 + Real.sqrt 3) * (Real.sqrt L₁ + Real.sqrt L₂) := by
    nlinarith only [Real.sqrt_nonneg L₁]
  gcongr
  exact Real.rpow_nonneg ht.1.le _

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
  have h := two_point_coercivity_of_upper_dini_bound_interval
    (by norm_num : (0 : ℝ) < 1) hL₁ hL₂ hcont hac hzero hnonneg
    (by simpa only [Real.one_rpow, mul_one] using hdini)
  simpa only [div_one] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
