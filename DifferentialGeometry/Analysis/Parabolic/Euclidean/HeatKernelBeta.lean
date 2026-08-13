import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelDuhamel

noncomputable section

open MeasureTheory Real Set
open scoped Interval
namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

theorem scale12_int {a : ℝ} (_ha : 0 < a) :
    ∫ s : ℝ in 0..a, heatScale12 s = 2 * a ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

def critTime (t s : ℝ) : ℝ :=
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
theorem critTime_nonneg (t s : ℝ) : 0 ≤ critTime t s := by
  exact mul_nonneg (heatScale12_nonneg (t - s)) (heatScale12_nonneg s)
theorem leftCrit_intble {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (critTime t) volume 0 (t / 2) := by
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
private theorem rightCrit_intble {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (critTime t) volume (t / 2) t := by
  have hleft := leftCrit_intble ht
  have hhalf : t - t / 2 = t / 2 := by ring
  have hraw : IntervalIntegrable
      (fun x : ℝ => heatScale12 x * heatScale12 (t - x))
      volume (t / 2) t := by
    simpa only [critTime, hhalf, sub_zero, sub_sub_cancel] using
      hleft.symm.comp_sub_left t
  refine hraw.congr ?_
  intro x _
  unfold critTime
  rw [mul_comm]
theorem critTime_intble {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (critTime t) volume 0 t := by
  have hleft := leftCrit_intble ht
  have hright := rightCrit_intble ht
  exact hleft.trans hright

theorem rightCrit_eq_left {t : ℝ} :
    (∫ s : ℝ in t / 2..t, critTime t s) =
      ∫ s : ℝ in 0..t / 2, critTime t s := by
  have hhalf : t - t / 2 = t / 2 := by ring
  calc
    (∫ s : ℝ in t / 2..t, critTime t s)
        = ∫ s : ℝ in 0..t / 2, critTime t (t - s) := by
      symm
      have hreflect :=
        intervalIntegral.integral_comp_sub_left (f := critTime t)
          (a := 0) (b := t / 2) t
      convert hreflect using 1
      all_goals simp [hhalf]
    _ = ∫ s : ℝ in 0..t / 2, critTime t s := by
      apply intervalIntegral.integral_congr
      intro s _
      change heatScale12 (t - (t - s)) * heatScale12 (t - s) =
        heatScale12 (t - s) * heatScale12 s
      rw [show t - (t - s) = s by ring, mul_comm]
theorem leftCrit_int_le {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in 0..t / 2, critTime t s) ≤ 2 := by
  have hhalf : 0 < t / 2 := by positivity
  have hleft := leftCrit_intble ht
  have hpow : IntervalIntegrable heatScale12 volume 0 (t / 2) := by
    unfold heatScale12
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmajor : IntervalIntegrable
      (fun s : ℝ => heatScale12 (t / 2) * heatScale12 s) volume 0 (t / 2) :=
    hpow.const_mul _
  calc
    (∫ s : ℝ in 0..t / 2, critTime t s)
        ≤ ∫ s : ℝ in 0..t / 2, heatScale12 (t / 2) * heatScale12 s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hhalf.le hleft hmajor
      intro s hs
      have hdec : heatScale12 (t - s) ≤ heatScale12 (t / 2) := by
        unfold heatScale12
        exact Real.rpow_le_rpow_of_nonpos hhalf (by linarith [hs.2]) (by norm_num)
      exact mul_le_mul_of_nonneg_right hdec (heatScale12_nonneg s)
    _ = heatScale12 (t / 2) * (2 * (t / 2) ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, scale12_int hhalf]
    _ = 2 := by
      unfold heatScale12
      calc
        (t / 2) ^ (-(1 : ℝ) / 2) * (2 * (t / 2) ^ (1 / 2 : ℝ))
            = 2 * ((t / 2) ^ (-(1 : ℝ) / 2) * (t / 2) ^ (1 / 2 : ℝ)) := by
          ring
        _ = 2 * (t / 2) ^ (-(1 : ℝ) / 2 + 1 / 2) := by
          rw [Real.rpow_add hhalf]
        _ = 2 := by norm_num

theorem critTime_int_le {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in 0..t, critTime t s) ≤ 4 := by
  have hleft := leftCrit_intble ht
  have hright := rightCrit_intble ht
  calc
    (∫ s : ℝ in 0..t, critTime t s)
        = (∫ s : ℝ in 0..t / 2, critTime t s) +
            ∫ s : ℝ in t / 2..t, critTime t s :=
      (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
    _ = 2 * (∫ s : ℝ in 0..t / 2, critTime t s) := by
      rw [rightCrit_eq_left]
      ring
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (leftCrit_int_le ht) (by norm_num)
    _ = 4 := by norm_num

theorem critCoeff_int_le {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K) :
    (∫ s : ℝ in 0..t, K * critTime t s) ≤ 4 * K := by
  calc
    (∫ s : ℝ in 0..t, K * critTime t s)
        = K * ∫ s : ℝ in 0..t, critTime t s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * 4 := mul_le_mul_of_nonneg_left (critTime_int_le ht) hK
    _ = 4 * K := by ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
