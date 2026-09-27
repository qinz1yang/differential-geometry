import DifferentialGeometry.Analysis.Estimates.IteratedApproximationError

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped BigOperators

theorem exists_half_pow_le_three_quarter_pow (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      β * (1 / 2 : ℝ) ^ s ≤ (3 / 4 : ℝ) ^ s / 16 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < 1 / (16 * β) by positivity) (show (2 / 3 : ℝ) < 1 by norm_num)
  refine ⟨N, fun s hs => ?_⟩
  have hpow : (2 / 3 : ℝ) ^ s ≤ 1 / (16 * β) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hs).trans hN.le
  have hratio : β * (2 / 3 : ℝ) ^ s ≤ 1 / 16 := by
    have h := (le_div_iff₀ (show 0 < 16 * β by positivity)).mp hpow
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ (3 / 4 : ℝ) ^ s by positivity)
  have hid : (2 / 3 : ℝ) ^ s * (3 / 4 : ℝ) ^ s = (1 / 2 : ℝ) ^ s := by
    rw [← mul_pow]
    norm_num
  nlinarith [hid]

end DifferentialGeometry.CheegerGromovCompactness
