import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Real

namespace Real

theorem neg_log_cos_le_sq_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    -log (cos t) ≤ t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have hc : (1 / 2 : ℝ) ≤ cos t := by linarith [one_sub_sq_div_two_le_cos (x := t)]
  have hcp : 0 < cos t := by linarith
  have hl := one_sub_inv_le_log_of_pos hcp
  have hinv : (cos t)⁻¹ - 1 ≤ t ^ 2 := by
    have hh : 1 - cos t ≤ t ^ 2 * cos t := by
      nlinarith [one_sub_sq_div_two_le_cos (x := t), sq_nonneg t]
    apply (sub_le_iff_le_add).mpr
    rw [← one_div]
    apply (div_le_iff₀ hcp).mpr
    nlinarith
  linarith

end Real
