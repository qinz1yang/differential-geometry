import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.AngleEstimates

set_option autoImplicit false

namespace Real

private theorem sq_sub_le_pi_sq_mul_cos_sub_of_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hab : a ≤ b) :
    2 * (b - a) ^ 2 ≤ Real.pi ^ 2 * (cos a - cos b) := by
  have hd : 0 ≤ (b - a) / 2 := by linarith
  have hdp : (b - a) / 2 ≤ Real.pi / 2 := by linarith
  have hsin : sin ((b - a) / 2) ≤ sin ((a + b) / 2) := by
    by_cases hmid : (a + b) / 2 ≤ Real.pi / 2
    · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hmid (by linarith)
    · rw [← sin_pi_sub ((a + b) / 2)]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
        (by linarith) (by linarith)
  have hs0 : 0 ≤ sin ((b - a) / 2) := sin_nonneg_of_nonneg_of_le_pi hd (by linarith [pi_pos])
  have hprod := mul_le_mul_of_nonneg_right hsin hs0
  have hj := mul_le_sin hd hdp
  have hjsq := pow_le_pow_left₀ (show 0 ≤ 2 / Real.pi * ((b - a) / 2) by positivity) hj 2
  have hid : cos a - cos b = 2 * sin ((a + b) / 2) * sin ((b - a) / 2) := by
    rw [cos_sub_cos]
    have heq : (a - b) / 2 = -((b - a) / 2) := by ring
    rw [heq, sin_neg]
    ring
  have hj' : (b - a) ^ 2 ≤ Real.pi ^ 2 * sin ((b - a) / 2) ^ 2 := by
    field_simp at hjsq
    nlinarith
  rw [hid]
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hprod)]

theorem sq_sub_le_pi_sq_mul_abs_cos_sub {a b : ℝ}
    (ha : a ∈ Set.Icc 0 Real.pi) (hb : b ∈ Set.Icc 0 Real.pi) :
    2 * (a - b) ^ 2 ≤ Real.pi ^ 2 * |cos a - cos b| := by
  rcases le_total a b with hab | hba
  · have h := sq_sub_le_pi_sq_mul_cos_sub_of_le ha.1 hb.2 hab
    have hc := cos_le_cos_of_nonneg_of_le_pi ha.1 hb.2 hab
    rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    nlinarith
  · have h := sq_sub_le_pi_sq_mul_cos_sub_of_le hb.1 ha.2 hba
    have hc := cos_le_cos_of_nonneg_of_le_pi hb.1 ha.2 hba
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    nlinarith

theorem abs_sub_le_pi_mul_sqrt_of_abs_cos_sub_le {a b ε : ℝ}
    (ha : a ∈ Set.Icc 0 Real.pi) (hb : b ∈ Set.Icc 0 Real.pi)
    (hcos : |cos a - cos b| ≤ 2 * ε) :
    |a - b| ≤ Real.pi * sqrt ε := by
  have hε : 0 ≤ ε := by linarith [abs_nonneg (cos a - cos b)]
  have h := sq_sub_le_pi_sq_mul_abs_cos_sub ha hb
  have hm := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
  have hs := sq_sqrt hε
  have hnon : 0 ≤ Real.pi * sqrt ε := mul_nonneg pi_pos.le (sqrt_nonneg ε)
  have hsq : |a - b| ^ 2 ≤ (Real.pi * sqrt ε) ^ 2 := by
    rw [sq_abs, mul_pow, hs]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) hnon).mp hsq

end Real
