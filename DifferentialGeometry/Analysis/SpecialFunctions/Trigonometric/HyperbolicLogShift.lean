import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

namespace Real

theorem sinh_add_log_le_mul_sinh (A : ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    sinh (A + log q) ≤ q * sinh A := by
  have hsq : q ^ 2 ≤ 1 := by nlinarith
  have hneg : q * exp (-A) ≤ exp (-A) / q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith [mul_nonneg (exp_pos (-A)).le (sub_nonneg.mpr hsq)]
  have hne : exp (-(A + log q)) = exp (-A) / q := by
    rw [show -(A + log q) = -A - log q by ring, exp_sub, exp_log hq]
  rw [sinh_eq, exp_add, exp_log hq, hne, sinh_eq]
  linarith

theorem add_log_le_of_mul_sinh_le {A C q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (h : q * sinh A ≤ sinh C) : A + log q ≤ C :=
  sinh_le_sinh.mp ((sinh_add_log_le_mul_sinh A hq hq1).trans h)

end Real
