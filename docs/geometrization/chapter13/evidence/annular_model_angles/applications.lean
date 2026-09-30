import DifferentialGeometry.Geometry.Comparison.TriangleExcessAngle
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace AnnularRegression

theorem unequal_flat_triangle :
    1 + cos (comparisonAngleNegCurvature (0 ^ 2) 2 3 (49 / 10)) ≤ 1 / 12 := by
  have h := one_add_cos_comparisonAngle_le_excess (κ := 0) (a := 2) (b := 3) (c := 49 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem curved_zero_excess {κ a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    1 + cos (comparisonAngleNegCurvature (κ ^ 2) a b (a + b)) = 0 := by
  have h := one_add_cos_comparisonAngle_le_excess hκ ha hb
    (by rw [abs_le]; constructor <;> linarith : |a - b| ≤ a + b) le_rfl
  have hl := neg_one_le_cos (comparisonAngleNegCurvature (κ ^ 2) a b (a + b))
  simp only [sub_self, mul_zero, zero_mul, zero_div] at h
  linarith

theorem annular_original_budget_at_curvature_boundary :
    Real.pi - Real.pi / 3 <
      comparisonAngleNegCurvature ((1 / 3 : ℝ) ^ 2) (2 * 1 / 5) (2 * 1 / 5) (799 / 1000) := by
  apply pi_sub_lt_comparisonAngle_annular (a := 1) (δ := 1 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity)
  rw [cos_pi_div_three]
  norm_num

theorem mixed_arm_original_constant {κ a b c : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (hlo : |a - b| ≤ c)
    (hhi : c ≤ a + b) (hsmall : κ * (a + b) ≤ 1) :
    1 + cos (comparisonAngleNegCurvature (κ ^ 2) a b c) ≤
      2 * (a + b - c) * (1 / a + 1 / b) := by
  have h := one_add_cos_comparisonAngle_le_excess hκ ha hb hlo hhi
  have hcosh : cosh (κ * (a + b)) ≤ 2 := by
    have hx : 0 ≤ κ * (a + b) := mul_nonneg hκ (add_pos ha hb).le
    have he := cosh_sub_one_le_sq hx hsmall
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - κ * (a + b) by linarith)]
  apply h.trans
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  have hright : 2 * (a + b - c) * (1 / a + 1 / b) * (a * b) =
      2 * (a + b - c) * (a + b) := by field_simp; ring
  rw [hright]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcosh (sub_nonneg.mpr hhi)) (add_pos ha hb).le

#print axioms unequal_flat_triangle
#print axioms curved_zero_excess
#print axioms annular_original_budget_at_curvature_boundary
#print axioms mixed_arm_original_constant
end AnnularRegression
