import DifferentialGeometry.Geometry.Comparison.PairedChartQuality

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def pairedChartDistortion (n : ℕ) : ℝ :=
  max (sqrt n) ((100 * Real.pi / pairedChartQuality n 1) ^ 2)

theorem pairedChartDistortion_pos (n : ℕ) : 0 < pairedChartDistortion n := by
  have h : 0 < (100 * Real.pi / pairedChartQuality n 1) ^ 2 := by
    exact sq_pos_of_pos (div_pos (by positivity) (pairedChartQuality_pos n 1))
  exact h.trans_le (le_max_right _ _)

theorem sqrt_le_pairedChartDistortion {m n : ℕ} (hmn : m ≤ n) :
    sqrt m ≤ pairedChartDistortion n :=
  (sqrt_le_sqrt (show (m : ℝ) ≤ n by exact_mod_cast hmn)).trans (le_max_left _ _)

theorem inverse_pairedChartDistortion_le_quality {n k : ℕ} (hk : 1 ≤ k) :
    (pairedChartDistortion n)⁻¹ ≤ (pairedChartQuality n k / (100 * Real.pi)) ^ 2 := by
  have ht := pairedChartQuality_pos n 1
  have hs := pairedChartQuality_pos n k
  have hmono := pairedChartQuality_mono n hk
  have hpi : 0 < 100 * Real.pi := by positivity
  have hpos : 0 < (100 * Real.pi / pairedChartQuality n 1) ^ 2 := by positivity
  have h := (inv_le_inv₀ (pairedChartDistortion_pos n) hpos).mpr (le_max_right _ _)
  have heq : ((100 * Real.pi / pairedChartQuality n 1) ^ 2)⁻¹ =
      (pairedChartQuality n 1 / (100 * Real.pi)) ^ 2 := by
    field_simp
  rw [heq] at h
  exact h.trans (pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right hmono hpi.le) 2)

end DifferentialGeometry.Geometry.Comparison.Toponogov
