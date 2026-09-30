import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem one_add_cos_comparisonAngle_le_excess
    {κ a b c : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (hlo : |a - b| ≤ c) (hhi : c ≤ a + b) :
    1 + cos (comparisonAngleNegCurvature (κ ^ 2) a b c) ≤
      cosh (κ * (a + b)) * (a + b - c) * (a + b) / (a * b) := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hlo
  have he : 0 ≤ a + b - c := sub_nonneg.mpr hhi
  rcases hκ.eq_or_lt with hκ | hκ
  · subst κ
    simp only [zero_pow (by decide : 2 ≠ 0), comparisonAngleNegCurvature_zero,
      zero_mul, cosh_zero, one_mul]
    rw [cos_comparisonAngle ha hb hlo hhi]
    apply (le_div_iff₀ (mul_pos ha hb)).mpr
    have hq := div_mul_cancel₀ (a ^ 2 + b ^ 2 - c ^ 2)
      (show 2 * a * b ≠ 0 by positivity)
    nlinarith [sq_nonneg (a + b - c)]
  · have hs1 : 0 < sinh (κ * a) := sinh_pos_iff.mpr (mul_pos hκ ha)
    have hs2 : 0 < sinh (κ * b) := sinh_pos_iff.mpr (mul_pos hκ hb)
    have hden : 0 < sinh (κ * a) * sinh (κ * b) := mul_pos hs1 hs2
    have hlow : κ ^ 2 * (a * b) ≤ sinh (κ * a) * sinh (κ * b) := by
      have h := mul_le_mul (self_le_sinh_iff.mpr (mul_pos hκ ha).le)
        (self_le_sinh_iff.mpr (mul_pos hκ hb).le) (mul_pos hκ hb).le hs1.le
      nlinarith
    have hnum : cosh (κ * (a + b)) - cosh (κ * c) ≤
        κ ^ 2 * (cosh (κ * (a + b)) * (a + b - c) * (a + b)) := by
      have h := cosh_sub_le_sinh_mul_sub (mul_nonneg hκ.le hc)
        (mul_le_mul_of_nonneg_left hhi hκ.le) le_rfl
      have hs := sinh_le_self_mul_cosh (mul_nonneg hκ.le (add_pos ha hb).le) le_rfl
      have hm := mul_le_mul_of_nonneg_right hs (mul_nonneg hκ.le he)
      nlinarith
    have hcos := cos_comparisonAngleNegCurvature_of_pos (sq_pos_of_pos hκ) ha hb hlo hhi
    rw [sqrt_sq hκ.le] at hcos
    have hid : 1 + cos (comparisonAngleNegCurvature (κ ^ 2) a b c) =
        (cosh (κ * (a + b)) - cosh (κ * c)) / (sinh (κ * a) * sinh (κ * b)) := by
      rw [hcos, one_add_div hden.ne', mul_add, cosh_add]
      congr 1
      ring
    rw [hid]
    calc
      _ ≤ (κ ^ 2 * (cosh (κ * (a + b)) * (a + b - c) * (a + b))) /
          (sinh (κ * a) * sinh (κ * b)) := div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (κ ^ 2 * (cosh (κ * (a + b)) * (a + b - c) * (a + b))) /
          (κ ^ 2 * (a * b)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
      _ = _ := by rw [mul_div_mul_left _ _ (sq_pos_of_pos hκ).ne']

theorem one_add_cos_comparisonAngle_equal_le_small
    {κ r c : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hc : 0 ≤ c)
    (hc2 : c ≤ 2 * r) (hκr : κ * r ≤ 2 / 15) :
    1 + cos (comparisonAngleNegCurvature (κ ^ 2) r r c) ≤
      (12 / 5) * (2 * r - c) / r := by
  have hx : 0 ≤ κ * (r + r) := mul_nonneg hκ (add_pos hr hr).le
  have hx1 : κ * (r + r) ≤ 1 := by nlinarith
  have hcosh : cosh (κ * (r + r)) ≤ 6 / 5 := by
    have h := cosh_sub_one_le_sq hx hx1
    have hsmall : κ * (r + r) ≤ 4 / 15 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ 4 / 15 - κ * (r + r) by linarith)
      (show 0 ≤ 4 / 15 + κ * (r + r) by linarith)]
  have h := one_add_cos_comparisonAngle_le_excess hκ hr hr
    (by simpa only [sub_self, abs_zero] using hc) (by linarith : c ≤ r + r)
  apply h.trans
  apply (div_le_iff₀ (mul_pos hr hr)).mpr
  have hq := div_mul_cancel₀ ((12 / 5) * (2 * r - c)) hr.ne'
  have hm := mul_le_mul_of_nonneg_right hcosh
    (mul_nonneg (show 0 ≤ 2 * r - c by linarith) (show 0 ≤ 2 * r by linarith))
  nlinarith


theorem pi_sub_lt_comparisonAngle_annular
    {κ r a c δ τ : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (har : a ≤ r)
    (hc : 0 ≤ c) (hcr : c ≤ 4 * r / 5) (hκr : κ * r ≤ 1 / 3)
    (hexcess : 4 * r / 5 - c < 15 * δ) (hτ : 0 ≤ τ)
    (hbudget : 90 * δ / a < 1 - cos τ) :
    Real.pi - τ < comparisonAngleNegCurvature (κ ^ 2) (2 * r / 5) (2 * r / 5) c := by
  have hr : 0 < r := ha.trans_le har
  have hδ : 0 < δ := by linarith
  have h := one_add_cos_comparisonAngle_equal_le_small hκ
    (by positivity : 0 < 2 * r / 5) hc (by linarith) (by nlinarith)
  have heq : (12 / 5) * (2 * (2 * r / 5) - c) / (2 * r / 5) =
      6 * (4 * r / 5 - c) / r := by
    field_simp
    ring
  rw [heq] at h
  have hsmall : 1 + cos (comparisonAngleNegCurvature (κ ^ 2) (2 * r / 5) (2 * r / 5) c) <
      1 - cos τ := by
    calc
      _ ≤ 6 * (4 * r / 5 - c) / r := h
      _ < 90 * δ / r := (div_lt_div_iff_of_pos_right hr).mpr (by linarith)
      _ ≤ 90 * δ / a := div_le_div_of_nonneg_left (by positivity) ha har
      _ < _ := hbudget
  by_contra hn
  have hh := cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngleNegCurvature_mem_Icc (κ ^ 2) (2 * r / 5) (2 * r / 5) c).1
    (show Real.pi - τ ≤ Real.pi by linarith) (le_of_not_gt hn)
  rw [cos_pi_sub] at hh
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
