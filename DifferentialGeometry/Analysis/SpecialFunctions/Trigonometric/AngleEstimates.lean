import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Real

theorem sq_div_four_le_one_sub_cos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 / 4 ≤ 1 - cos x := by
  have hxhalf : 0 ≤ x / 2 := by linarith
  have hsq : (x / 2) ^ 2 ≤ 1 := by nlinarith
  have hcube : (x / 2) ^ 3 ≤ x / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hsq hxhalf]
  have hsin : 3 * x / 8 ≤ sin (x / 2) := by
    nlinarith [sin_ge_sub_cube hxhalf]
  have hsin2 := pow_le_pow_left₀ (show 0 ≤ 3 * x / 8 by positivity) hsin 2
  rw [sin_sq_eq_half_sub] at hsin2
  have hdouble : 2 * (x / 2) = x := by ring
  rw [hdouble] at hsin2
  nlinarith

theorem pi_sub_four_mul_le_of_one_add_cos_le {δ θ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) (hθ : 0 ≤ θ)
    (hcos : 1 + cos θ ≤ 4 * δ ^ 2) : Real.pi - 4 * δ ≤ θ := by
  have hlower := sq_div_four_le_one_sub_cos (show 0 ≤ 4 * δ by positivity)
    (show 4 * δ ≤ 1 by linarith)
  by_contra h
  have ht := cos_lt_cos_of_nonneg_of_le_pi hθ (show Real.pi - 4 * δ ≤ Real.pi by linarith)
    (lt_of_not_ge h)
  rw [cos_pi_sub] at ht
  nlinarith

end Real
