import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

open Set

namespace Complex

theorem norm_one_sub_mul_exp_mul_I_sq (ρ θ : ℝ) :
    ‖1 - (ρ : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 = 1 + ρ ^ 2 - 2 * ρ * Real.cos θ := by
  rw [Complex.sq_norm, normSq_sub]
  simp [normSq_eq_norm_sq]
  ring

theorem norm_one_sub_mul_exp_arccos (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ‖1 - (ρ : ℂ) * exp ((Real.arccos (ρ / 2) : ℂ) * I)‖ = 1 := by
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hsq := norm_one_sub_mul_exp_mul_I_sq ρ (Real.arccos (ρ / 2))
  rw [hcos] at hsq
  nlinarith [norm_nonneg (1 - (ρ : ℂ) * exp ((Real.arccos (ρ / 2) : ℂ) * I))]

theorem norm_one_sub_mul_exp_neg_arccos (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ‖1 - (ρ : ℂ) * exp (((-Real.arccos (ρ / 2) : ℝ) : ℂ) * I)‖ = 1 := by
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hsq := norm_one_sub_mul_exp_mul_I_sq ρ (-Real.arccos (ρ / 2))
  rw [Real.cos_neg, hcos] at hsq
  nlinarith [norm_nonneg (1 - (ρ : ℂ) * exp (((-Real.arccos (ρ / 2) : ℝ) : ℂ) * I))]

theorem one_sub_mul_exp_mem_closedBall (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    1 - (ρ : ℂ) * exp ((θ : ℂ) * I) ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have habs : |θ| ≤ Real.arccos (ρ / 2) := abs_le.mpr hθ
  have hcosle := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (Real.arccos_le_pi (ρ / 2)) habs
  rw [Real.cos_abs, hcos] at hcosle
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq := norm_one_sub_mul_exp_mul_I_sq ρ θ
  nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hcosle),
    norm_nonneg (1 - (ρ : ℂ) * exp ((θ : ℂ) * I))]

theorem one_sub_mul_exp_mem_ball (ρ : ℝ) (hρ0 : 0 < ρ)
    {θ : ℝ} (hθ : θ ∈ Ioo (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    1 - (ρ : ℂ) * exp ((θ : ℂ) * I) ∈ Metric.ball (0 : ℂ) 1 := by
  have habs : |θ| < Real.arccos (ρ / 2) := abs_lt.mpr hθ
  have hhalf : ρ / 2 < 1 := Real.arccos_pos.mp ((abs_nonneg θ).trans_lt habs)
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) hhalf.le
  have hcoslt := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (Real.arccos_le_pi (ρ / 2)) habs
  rw [Real.cos_abs, hcos] at hcoslt
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := norm_one_sub_mul_exp_mul_I_sq ρ θ
  nlinarith [mul_pos hρ0 (sub_pos.mpr hcoslt),
    norm_nonneg (1 - (ρ : ℂ) * exp ((θ : ℂ) * I))]

theorem dist_one_sub_mul_exp_one (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    dist (1 - (ρ : ℂ) * exp ((θ : ℂ) * I)) 1 = ρ := by
  rw [dist_eq_norm]
  have heq : 1 - (ρ : ℂ) * exp ((θ : ℂ) * I) - 1 =
      -((ρ : ℂ) * exp ((θ : ℂ) * I)) := by ring
  rw [heq, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I,
    mul_one, abs_of_nonneg hρ]

theorem norm_circleMap_neg_one_arccos (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ‖circleMap (-1) ρ (Real.arccos (ρ / 2))‖ = 1 := by
  rw [circleMap, neg_add_eq_sub, ← norm_neg, neg_sub]
  exact norm_one_sub_mul_exp_arccos ρ hρ0 hρ2

theorem norm_circleMap_neg_one_neg_arccos (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ‖circleMap (-1) ρ (-Real.arccos (ρ / 2))‖ = 1 := by
  rw [circleMap, neg_add_eq_sub, ← norm_neg, neg_sub]
  exact norm_one_sub_mul_exp_neg_arccos ρ hρ0 hρ2

theorem circleMap_neg_one_mem_closedBall (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    circleMap (-1) ρ θ ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, circleMap]
  have hq : ‖1 - (ρ : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (one_sub_mul_exp_mem_closedBall ρ hρ0 hρ2 hθ)
  calc
    ‖(-1 : ℂ) + (ρ : ℂ) * exp ((θ : ℂ) * I)‖ =
        ‖-(1 - (ρ : ℂ) * exp ((θ : ℂ) * I))‖ := by congr 1; ring
    _ = ‖1 - (ρ : ℂ) * exp ((θ : ℂ) * I)‖ := norm_neg _
    _ ≤ 1 := hq

theorem circleMap_neg_one_mem_ball (ρ : ℝ) (hρ0 : 0 < ρ)
    {θ : ℝ} (hθ : θ ∈ Ioo (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    circleMap (-1) ρ θ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right, circleMap]
  have hq : ‖1 - (ρ : ℂ) * exp ((θ : ℂ) * I)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (one_sub_mul_exp_mem_ball ρ hρ0 hθ)
  calc
    ‖(-1 : ℂ) + (ρ : ℂ) * exp ((θ : ℂ) * I)‖ =
        ‖-(1 - (ρ : ℂ) * exp ((θ : ℂ) * I))‖ := by congr 1; ring
    _ = ‖1 - (ρ : ℂ) * exp ((θ : ℂ) * I)‖ := norm_neg _
    _ < 1 := hq

end Complex

end

section

theorem circleMap_neg_one_two_mul_cos (a : ℝ) :
    circleMap (-1) (2 * Real.cos a) a = circleMap 0 1 (2 * a) := by
  rw [show circleMap (-1) (2 * Real.cos a) a =
      -1 + circleMap 0 (2 * Real.cos a) a by simp only [circleMap, zero_add]]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.one_re,
      circleMap_zero_re, Real.cos_two_mul]
    ring
  · simp only [Complex.add_im, Complex.neg_im, Complex.one_im,
      circleMap_zero_im, Real.sin_two_mul]
    ring

theorem circleMap_neg_one_arccos {ρ : ℝ} (hρ : -2 ≤ ρ) (hρ2 : ρ ≤ 2) :
    circleMap (-1) ρ (Real.arccos (ρ / 2)) =
      circleMap 0 1 (2 * Real.arccos (ρ / 2)) := by
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have h := circleMap_neg_one_two_mul_cos (Real.arccos (ρ / 2))
  rw [hcos, show 2 * (ρ / 2) = ρ by ring] at h
  exact h

theorem circleMap_neg_one_neg_arccos {ρ : ℝ} (hρ : -2 ≤ ρ) (hρ2 : ρ ≤ 2) :
    circleMap (-1) ρ (-Real.arccos (ρ / 2)) =
      circleMap 0 1 (2 * Real.pi - 2 * Real.arccos (ρ / 2)) := by
  have h := circleMap_neg_one_two_mul_cos (-Real.arccos (ρ / 2))
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  rw [Real.cos_neg, hcos, show 2 * (ρ / 2) = ρ by ring] at h
  rw [h, show 2 * Real.pi - 2 * Real.arccos (ρ / 2) =
      2 * (-Real.arccos (ρ / 2)) + 2 * Real.pi by ring, periodic_circleMap]

namespace Real

theorem pi_sub_two_mul_arccos_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < π - 2 * arccos (ρ / 2) := by
  have h := arccos_lt_pi_div_two.mpr (show 0 < ρ / 2 by linarith)
  linarith

theorem pi_sub_two_mul_arccos_lt_pi_div_three {ρ : ℝ} (hρ : ρ < 1) :
    π - 2 * arccos (ρ / 2) < π / 3 := by
  have heq : arccos (1 / 2 : ℝ) = π / 3 := by
    rw [← cos_pi_div_three]
    exact arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
  by_cases hρ2 : -2 ≤ ρ
  · have h := arccos_lt_arccos (show -1 ≤ ρ / 2 by linarith)
      (show ρ / 2 < (1 / 2 : ℝ) by linarith) (by norm_num)
    rw [heq] at h
    linarith
  · rw [arccos_of_le_neg_one (by linarith : ρ / 2 ≤ -1)]
    linarith [pi_pos]

theorem self_le_pi_sub_two_mul_arccos {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ρ ≤ π - 2 * arccos (ρ / 2) := by
  have hangle : arccos (ρ / 2) ≤ π / 2 := arccos_le_pi_div_two.mpr (by linarith)
  have h := sin_le (show 0 ≤ π / 2 - arccos (ρ / 2) by linarith)
  rw [sin_pi_div_two_sub, cos_arccos (by linarith) (by linarith)] at h
  linarith

theorem one_sub_two_mul_arccos_div_pi_lt_one_third {ρ : ℝ} (hρ : ρ < 1) :
    1 - 2 * arccos (ρ / 2) / π < 1 / 3 := by
  have h := pi_sub_two_mul_arccos_lt_pi_div_three hρ
  have heq : 1 - 2 * arccos (ρ / 2) / π =
      (π - 2 * arccos (ρ / 2)) / π := by
    field_simp
  rw [heq]
  apply (div_lt_iff₀ pi_pos).mpr
  linarith

theorem Icc_subset_arccos_div_pi {r ρ : ℝ} (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    Set.Icc (1 / 2 - r / (2 * π)) (1 / 2 + r / (2 * π)) ⊆
      Set.Icc (arccos (ρ / 2) / π) (1 - arccos (ρ / 2) / π) := by
  have h := self_le_pi_sub_two_mul_arccos hρ hρ2
  have hdivide := div_le_div_of_nonneg_right (hrρ.trans h)
    (show 0 ≤ 2 * π by positivity)
  have heq : (π - 2 * arccos (ρ / 2)) / (2 * π) =
      1 / 2 - arccos (ρ / 2) / π := by
    field_simp
  rw [heq] at hdivide
  apply Set.Icc_subset_Icc <;> linarith

end Real

end
