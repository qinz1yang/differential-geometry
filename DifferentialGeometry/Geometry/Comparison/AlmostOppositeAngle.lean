import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem one_add_cos_comparisonAngle_double_le
    {κ r ℓ μ : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hrℓ : r ≤ ℓ)
    (hℓ : ℓ ≤ (1 + μ) * r) (hκr : κ * r ≤ 1 / 3) :
    0 ≤ 1 + cos (comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r)) ∧
      1 + cos (comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r)) ≤ 6 * μ := by
  have hℓ0 : 0 < ℓ := hr.trans_le hrℓ
  have hℓ2 : ℓ ≤ 2 * r := by nlinarith
  have hlo : |r - ℓ| ≤ 2 * r := by rw [abs_of_nonpos (sub_nonpos.mpr hrℓ)]; linarith
  have hup : 2 * r ≤ r + ℓ := by linarith
  refine ⟨by linarith [neg_one_le_cos (comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r))], ?_⟩
  rcases hκ.eq_or_lt with hκ | hκ
  · subst κ
    simp only [zero_pow (by decide : 2 ≠ 0), comparisonAngleNegCurvature_zero]
    rw [cos_comparisonAngle hr hℓ0 hlo hup]
    have hprod := mul_nonneg (show 0 ≤ ℓ - r by linarith)
      (show 0 ≤ 2 * r - ℓ by linarith)
    have hmr := mul_le_mul_of_nonneg_left hℓ hr.le
    have hscale := mul_le_mul_of_nonneg_left hrℓ (show 0 ≤ 6 * μ * r by positivity)
    have hq : (r ^ 2 + ℓ ^ 2 - (2 * r) ^ 2) / (2 * r * ℓ) ≤ 6 * μ - 1 := by
      apply (div_le_iff₀ (show 0 < 2 * r * ℓ by positivity)).mpr
      nlinarith
    linarith
  · have hx : 0 < κ * r := mul_pos hκ hr
    have hy : 0 < κ * ℓ := mul_pos hκ hℓ0
    have hxy : κ * r ≤ κ * ℓ := mul_le_mul_of_nonneg_left hrℓ hκ.le
    have hylim : κ * ℓ ≤ (1 + μ) * (κ * r) := by nlinarith [mul_le_mul_of_nonneg_left hℓ hκ.le]
    have hy2 : κ * ℓ ≤ 2 * (κ * r) := by nlinarith
    have hsum : κ * r + κ * ℓ ≤ 1 := by linarith
    have hc : cosh 1 ≤ 2 := by linarith [cosh_sub_one_le_sq (by norm_num : (0 : ℝ) ≤ 1) le_rfl]
    have hs : sinh (κ * r + κ * ℓ) ≤ 2 * (κ * r + κ * ℓ) :=
      (sinh_le_self_mul_cosh (add_nonneg hx.le hy.le) hsum).trans
        (by nlinarith [mul_le_mul_of_nonneg_left hc (add_nonneg hx.le hy.le)])
    have hn := cosh_sub_le_sinh_mul_sub (show 0 ≤ 2 * (κ * r) by positivity)
      (show 2 * (κ * r) ≤ κ * r + κ * ℓ by linarith) le_rfl
    have hn' : cosh (κ * r + κ * ℓ) - cosh (2 * (κ * r)) ≤
        6 * μ * (κ * r) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hs (show 0 ≤ κ * ℓ - κ * r by linarith)
      have hleft := mul_le_mul_of_nonneg_left hy2 (show 0 ≤ κ * ℓ - κ * r by linarith)
      have hright := mul_le_mul_of_nonneg_left hylim hx.le
      nlinarith
    have hd : (κ * r) ^ 2 ≤ sinh (κ * r) * sinh (κ * ℓ) := by
      have hh := mul_le_mul (self_le_sinh_iff.mpr hx.le)
        (self_le_sinh_iff.mpr hy.le) hy.le (sinh_pos_iff.mpr hx).le
      nlinarith [mul_le_mul_of_nonneg_left hxy hx.le]
    have hlaw := cos_comparisonAngleNegCurvature_of_pos (sq_pos_of_pos hκ) hr hℓ0 hlo hup
    rw [sqrt_sq hκ.le] at hlaw
    have hden : 0 < sinh (κ * r) * sinh (κ * ℓ) :=
      mul_pos (sinh_pos_iff.mpr hx) (sinh_pos_iff.mpr hy)
    have hid := (eq_div_iff hden.ne').mp hlaw
    rw [cosh_add] at hn'
    have heq : κ * (2 * r) = 2 * (κ * r) := by ring
    rw [heq] at hid
    apply (mul_le_mul_iff_left₀ hden).mp
    have hb := mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 * μ by positivity)
    nlinarith

theorem pi_sub_lt_comparisonAngle_double
    {κ r ℓ μ τ : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hrℓ : r ≤ ℓ)
    (hℓ : ℓ ≤ (1 + μ) * r) (hκr : κ * r ≤ 1 / 3)
    (hτ : 0 ≤ τ) (hbudget : 6 * μ < 1 - cos τ) :
    Real.pi - τ < comparisonAngleNegCurvature (κ ^ 2) r ℓ (2 * r) := by
  have hbound := (one_add_cos_comparisonAngle_double_le hκ hr hμ hμ1 hrℓ hℓ hκr).2
  by_contra h
  have hc := cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngleNegCurvature_mem_Icc (κ ^ 2) r ℓ (2 * r)).1
    (show Real.pi - τ ≤ Real.pi by linarith) (le_of_not_gt h)
  rw [cos_pi_sub] at hc
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
