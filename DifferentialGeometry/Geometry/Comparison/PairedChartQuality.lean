import DifferentialGeometry.Geometry.Comparison.RankExclusionChart

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def pairedChartQuality (n k : ℕ) : ℝ :=
  200 ^ k / (400 * ((n : ℝ) + 1) * 200 ^ (n + 1))

theorem pairedChartQuality_pos (n k : ℕ) : 0 < pairedChartQuality n k := by
  unfold pairedChartQuality
  positivity

theorem pairedChartQuality_succ (n k : ℕ) : pairedChartQuality n (k + 1) = 200 * pairedChartQuality n k := by
  unfold pairedChartQuality
  rw [pow_succ]
  ring

theorem pairedChartQuality_mono (n : ℕ) : Monotone (pairedChartQuality n) := by
  intro i j hij
  unfold pairedChartQuality
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) (by positivity)

theorem pairedChartQuality_top (n : ℕ) : pairedChartQuality n (n + 1) = 1 / (400 * ((n : ℝ)+1)) := by
  unfold pairedChartQuality
  field_simp

theorem pairedChartQuality_le (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    pairedChartQuality n k ≤ 1 / (400 * ((n : ℝ)+1)) := by
  exact (pairedChartQuality_mono n hk).trans_eq (pairedChartQuality_top n)

theorem pairedChartQuality_le_rank_bound (n : ℕ) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ n + 1) :
    pairedChartQuality n k ≤ 1 / (200 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkn : (k : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hk
  exact (pairedChartQuality_le n hk).trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))

theorem pairedChartQuality_eq_reciprocal (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    pairedChartQuality n k = 1 / (400 * ((n : ℝ)+1) * 200 ^ (n + 1-k)) := by
  unfold pairedChartQuality
  have hp : (200 : ℝ) ^ (n + 1) = 200 ^ k * 200 ^ (n + 1-k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hp]
  field_simp

end DifferentialGeometry.Geometry.Comparison.Toponogov
