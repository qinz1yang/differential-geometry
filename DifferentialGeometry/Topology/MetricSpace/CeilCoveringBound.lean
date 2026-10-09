import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Metric

theorem ceil_covering_bound_le_polynomial {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hεone : ε ≤ 1) (n : ℕ) :
    (((1 + Nat.ceil (B / ε)) ^ n : ℕ) : ℝ) ≤ (2 + B) ^ n * ε ^ (-(n : ℝ)) := by
  have hc := (Nat.ceil_lt_add_one (div_nonneg hB hε.le)).le
  have hb : (1 : ℝ) + Nat.ceil (B / ε) ≤ (2 + B) / ε := by
    have htwo : (2 : ℝ) ≤ 2 / ε := (le_div_iff₀ hε).mpr (by linarith)
    rw [add_div]
    linarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + Nat.ceil (B / ε)) hb n
  push_cast
  calc
    ((1 : ℝ) + Nat.ceil (B / ε)) ^ n ≤ ((2 + B) / ε) ^ n := hp
    _ = (2 + B) ^ n * ε ^ (-(n : ℝ)) := by
      rw [div_pow, Real.rpow_neg hε.le, Real.rpow_natCast, div_eq_mul_inv]

end Metric
