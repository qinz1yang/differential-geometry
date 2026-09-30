import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicLogShift
import Mathlib.Tactic.FieldSimp

namespace Real

theorem sinh_add_log_div_sinh {B q : ℝ} (hB : 0 < B) (hq : 0 < q) :
    sinh (B + log q) / sinh B = q - (q⁻¹ - q) / (exp (2 * B) - 1) := by
  have hEB : 0 < exp B := exp_pos B
  have hE2 : exp (2 * B) = exp B ^ 2 := by rw [two_mul, exp_add]; ring
  have hden : exp B ^ 2 - 1 ≠ 0 := by
    rw [← hE2]
    exact (sub_pos.mpr (one_lt_exp_iff.mpr (by linarith))).ne'
  have hm : exp (-(B + log q)) = exp (-B) / q := by
    rw [show -(B + log q) = -B - log q by ring, exp_sub, exp_log hq]
  rw [sinh_eq, exp_add, exp_log hq, hm, sinh_eq, exp_neg, hE2]
  field_simp
  ring

end Real
