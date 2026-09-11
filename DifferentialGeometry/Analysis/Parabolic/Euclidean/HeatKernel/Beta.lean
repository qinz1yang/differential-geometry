import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.Basic

noncomputable section

open MeasureTheory Real Set
open scoped Interval
namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

theorem scale12_int {a : ℝ} :
    ∫ s : ℝ in 0..a, heatScale12 s = 2 * a ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

def criticalTimeKernel (t s : ℝ) : ℝ :=
  heatScale12 (t - s) * heatScale12 s
private theorem heatScale12_nonneg (s : ℝ) : 0 ≤ heatScale12 s := by
  unfold heatScale12
  rcases le_total 0 s with hs | hs
  · exact Real.rpow_nonneg hs _
  · by_cases hs0 : s = 0
    · subst s
      rw [Real.zero_rpow (by norm_num : (-(1 : ℝ) / 2) ≠ 0)]
    · rw [Real.rpow_def_of_nonpos hs, if_neg hs0]
      have hcos : Real.cos ((-(1 : ℝ) / 2) * Real.pi) = 0 := by
        rw [show (-(1 : ℝ) / 2) * Real.pi = -(Real.pi / 2) by ring,
          Real.cos_neg, Real.cos_pi_div_two]
      rw [hcos, mul_zero]
theorem criticalTimeKernel_nonneg (t s : ℝ) : 0 ≤ criticalTimeKernel t s := by
  exact mul_nonneg (heatScale12_nonneg (t - s)) (heatScale12_nonneg s)
theorem criticalTimeKernel_integrable_left {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (criticalTimeKernel t) volume 0 (t / 2) := by
  have hhalf : 0 < t / 2 := by positivity
  have hpow : IntervalIntegrable heatScale12 volume 0 (t / 2) := by
    unfold heatScale12
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hcont : ContinuousOn (fun s : ℝ => heatScale12 (t - s)) [[0, t / 2]] := by
    unfold heatScale12
    refine (continuousOn_const.sub continuousOn_id).rpow_const ?_
    intro s hs
    left
    rw [uIcc_of_le hhalf.le] at hs
    exact (by linarith [hs.2, hhalf] : 0 < t - s).ne'
  exact hpow.continuousOn_mul hcont
private theorem criticalTimeKernel_integrable_right {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (criticalTimeKernel t) volume (t / 2) t := by
  have hleft := criticalTimeKernel_integrable_left ht
  have hhalf : t - t / 2 = t / 2 := by ring
  have hraw : IntervalIntegrable
      (fun x : ℝ => heatScale12 x * heatScale12 (t - x))
      volume (t / 2) t := by
    simpa only [criticalTimeKernel, hhalf, sub_zero, sub_sub_cancel] using
      hleft.symm.comp_sub_left t
  refine hraw.congr ?_
  intro x _
  unfold criticalTimeKernel
  rw [mul_comm]
theorem criticalTimeKernel_integrable {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (criticalTimeKernel t) volume 0 t := by
  have hleft := criticalTimeKernel_integrable_left ht
  have hright := criticalTimeKernel_integrable_right ht
  exact hleft.trans hright

theorem criticalTimeKernel_integral_right_eq_left {t : ℝ} :
    (∫ s : ℝ in t / 2..t, criticalTimeKernel t s) =
      ∫ s : ℝ in 0..t / 2, criticalTimeKernel t s := by
  have hhalf : t - t / 2 = t / 2 := by ring
  calc
    (∫ s : ℝ in t / 2..t, criticalTimeKernel t s)
        = ∫ s : ℝ in 0..t / 2, criticalTimeKernel t (t - s) := by
      symm
      have hreflect :=
        intervalIntegral.integral_comp_sub_left (f := criticalTimeKernel t)
          (a := 0) (b := t / 2) t
      convert hreflect using 1
      all_goals simp [hhalf]
    _ = ∫ s : ℝ in 0..t / 2, criticalTimeKernel t s := by
      apply intervalIntegral.integral_congr
      intro s _
      change heatScale12 (t - (t - s)) * heatScale12 (t - s) =
        heatScale12 (t - s) * heatScale12 s
      rw [show t - (t - s) = s by ring, mul_comm]
theorem criticalTimeKernel_integral_left_le {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in 0..t / 2, criticalTimeKernel t s) ≤ 2 := by
  have hhalf : 0 < t / 2 := by positivity
  have hleft := criticalTimeKernel_integrable_left ht
  have hpow : IntervalIntegrable heatScale12 volume 0 (t / 2) := by
    unfold heatScale12
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmajor : IntervalIntegrable
      (fun s : ℝ => heatScale12 (t / 2) * heatScale12 s) volume 0 (t / 2) :=
    hpow.const_mul _
  calc
    (∫ s : ℝ in 0..t / 2, criticalTimeKernel t s)
        ≤ ∫ s : ℝ in 0..t / 2, heatScale12 (t / 2) * heatScale12 s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hhalf.le hleft hmajor
      intro s hs
      have hdec : heatScale12 (t - s) ≤ heatScale12 (t / 2) := by
        unfold heatScale12
        exact Real.rpow_le_rpow_of_nonpos hhalf (by linarith [hs.2]) (by norm_num)
      exact mul_le_mul_of_nonneg_right hdec (heatScale12_nonneg s)
    _ = heatScale12 (t / 2) * (2 * (t / 2) ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, scale12_int]
    _ = 2 := by
      unfold heatScale12
      calc
        (t / 2) ^ (-(1 : ℝ) / 2) * (2 * (t / 2) ^ (1 / 2 : ℝ))
            = 2 * ((t / 2) ^ (-(1 : ℝ) / 2) * (t / 2) ^ (1 / 2 : ℝ)) := by
          ring
        _ = 2 * (t / 2) ^ (-(1 : ℝ) / 2 + 1 / 2) := by
          rw [Real.rpow_add hhalf]
        _ = 2 := by norm_num

theorem criticalTimeKernel_integral_le {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in 0..t, criticalTimeKernel t s) ≤ 4 := by
  have hleft := criticalTimeKernel_integrable_left ht
  have hright := criticalTimeKernel_integrable_right ht
  calc
    (∫ s : ℝ in 0..t, criticalTimeKernel t s)
        = (∫ s : ℝ in 0..t / 2, criticalTimeKernel t s) +
            ∫ s : ℝ in t / 2..t, criticalTimeKernel t s :=
      (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
    _ = 2 * (∫ s : ℝ in 0..t / 2, criticalTimeKernel t s) := by
      rw [criticalTimeKernel_integral_right_eq_left]
      ring
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (criticalTimeKernel_integral_left_le ht) (by norm_num)
    _ = 4 := by norm_num

theorem criticalTimeKernel_const_mul_integral_le {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K) :
    (∫ s : ℝ in 0..t, K * criticalTimeKernel t s) ≤ 4 * K := by
  calc
    (∫ s : ℝ in 0..t, K * criticalTimeKernel t s)
        = K * ∫ s : ℝ in 0..t, criticalTimeKernel t s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * 4 := mul_le_mul_of_nonneg_left (criticalTimeKernel_integral_le ht) hK
    _ = 4 * K := by ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
