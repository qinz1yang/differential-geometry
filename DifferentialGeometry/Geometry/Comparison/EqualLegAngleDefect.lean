import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem one_add_cos_comparisonAngle_equal_le
    {κ r c : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hc : 0 ≤ c)
    (hc2 : c ≤ 2 * r) (hκr : κ * r ≤ 1) :
    0 ≤ 1 + cos (comparisonAngleNegCurvature (κ ^ 2) r r c) ∧
      1 + cos (comparisonAngleNegCurvature (κ ^ 2) r r c) ≤ 4 * (2 * r - c) / r := by
  refine ⟨by linarith [neg_one_le_cos (comparisonAngleNegCurvature (κ ^ 2) r r c)], ?_⟩
  have he : 0 ≤ 2 * r - c := by linarith
  rcases hκ.eq_or_lt with hκ | hκ
  · subst κ
    simp only [zero_pow (by decide : 2 ≠ 0), comparisonAngleNegCurvature_zero]
    rw [cos_comparisonAngle hr hr (by simpa using hc) (by linarith)]
    apply (le_div_iff₀ hr).mpr
    have hquot : (r ^ 2 + r ^ 2 - c ^ 2) / (2 * r * r) * (2 * r * r) =
        r ^ 2 + r ^ 2 - c ^ 2 := div_mul_cancel₀ _ (by positivity)
    nlinarith [sq_nonneg (2 * r - c)]
  · have hx : 0 < κ * r := mul_pos hκ hr
    have hs : 0 < sinh (κ * r) := sinh_pos_iff.mpr hx
    have hcosh : cosh (κ * r) ≤ 2 := by
      have hh := cosh_sub_one_le_sq hx.le hκr
      nlinarith
    have hnum := cosh_sub_le_sinh_mul_sub (mul_nonneg hκ.le hc)
      (mul_le_mul_of_nonneg_left hc2 hκ.le) le_rfl
    rw [show κ * (2 * r) = 2 * (κ * r) by ring, sinh_two_mul] at hnum
    have hscale := mul_le_mul_of_nonneg_left hcosh (show 0 ≤ 2 * sinh (κ * r) * (κ * (2 * r - c)) by positivity)
    have hn : cosh (2 * (κ * r)) - cosh (κ * c) ≤
        4 * sinh (κ * r) * κ * (2 * r - c) := by nlinarith
    have hlaw := cos_comparisonAngleNegCurvature_of_pos (sq_pos_of_pos hκ) hr hr
      (by simpa using hc) (by linarith)
    rw [sqrt_sq hκ.le] at hlaw
    have hid := (eq_div_iff (show sinh (κ * r) * sinh (κ * r) ≠ 0 by positivity)).mp hlaw
    have hdouble : cosh (2 * (κ * r)) = cosh (κ * r) * cosh (κ * r) +
        sinh (κ * r) * sinh (κ * r) := by
      rw [two_mul, cosh_add]
    have hlow := self_le_sinh_iff.mpr hx.le
    have hm := mul_le_mul_of_nonneg_right hlow
      (show 0 ≤ 4 * sinh (κ * r) * (2 * r - c) by positivity)
    have hnr := mul_le_mul_of_nonneg_right hn hr.le
    apply (le_div_iff₀ hr).mpr
    apply (mul_le_mul_iff_left₀ (mul_pos hs hs)).mp
    nlinarith

theorem pi_sub_lt_comparisonAngle_equal
    {κ r c τ : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hc : 0 ≤ c)
    (hc2 : c ≤ 2 * r) (hκr : κ * r ≤ 1)
    (hτ : 0 ≤ τ) (hbudget : 4 * (2 * r - c) / r < 1 - cos τ) :
    Real.pi - τ < comparisonAngleNegCurvature (κ ^ 2) r r c := by
  have hbound := (one_add_cos_comparisonAngle_equal_le hκ hr hc hc2 hκr).2
  by_contra h
  have hh := cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngleNegCurvature_mem_Icc (κ ^ 2) r r c).1
    (show Real.pi - τ ≤ Real.pi by linarith) (le_of_not_gt h)
  rw [cos_pi_sub] at hh
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
