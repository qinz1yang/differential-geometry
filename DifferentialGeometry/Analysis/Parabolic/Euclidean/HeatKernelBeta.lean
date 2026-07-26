import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelDuhamel

/-!
# The critical first-heat-kernel time convolution

The divergence-refolded quasilinear arm couples the first heat derivative
`(t-s)^(-1/2)` with the rough gradient weight `s^(-1/2)`.  This convolution
is critical: its exact value is `pi`, independent of `t`.  For the fixed-point
estimate we only need the elementary uniform bound `4`, proved below by
splitting at `t/2`.

The important design consequence is explicit in the theorem statement:
there is no positive power of the horizon.  Contraction must therefore come
from a small `C^0` oscillation/coefficient difference, not from shrinking the
time interval.
-/

noncomputable section

open MeasureTheory Real Set

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

/-- Integral of the unreflected `s^(-1/2)` singularity. -/
theorem scale12_int {a : ℝ} (ha : 0 < a) :
    ∫ s : ℝ in 0..a, heatScale12 s = 2 * a ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [intervalIntegral.integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

/-- The critical convolution integrand. -/
def critTime (t s : ℝ) : ℝ :=
  heatScale12 (t - s) * heatScale12 s

theorem critTime_nonneg (t s : ℝ) : 0 ≤ critTime t s := by
  unfold critTime heatScale12
  exact mul_nonneg (Real.rpow_nonneg _ _) (Real.rpow_nonneg _ _)

/-- Integrability on the left half, where only the `s^(-1/2)` endpoint is
singular. -/
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
    exact (by linarith : 0 < t - s).ne'
  exact hpow.continuousOn_mul hcont

/-- The critical convolution is interval integrable on every positive
horizon. -/
theorem critTime_intble {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (critTime t) volume 0 t := by
  have hleft := leftCrit_intble ht
  have hhalf : t - t / 2 = t / 2 := by ring
  have hright : IntervalIntegrable (critTime t) volume (t / 2) t := by
    simpa [critTime, hhalf, mul_comm] using hleft.symm.comp_sub_left t
  exact hleft.trans hright

/-- Reflection around `t/2` exchanges the two halves of the critical
convolution. -/
theorem rightCrit_eq_left {t : ℝ} :
    (∫ s : ℝ in t / 2..t, critTime t s) =
      ∫ s : ℝ in 0..t / 2, critTime t s := by
  have hhalf : t - t / 2 = t / 2 := by ring
  calc
    (∫ s : ℝ in t / 2..t, critTime t s)
        = ∫ s : ℝ in 0..t / 2, critTime t (t - s) := by
      symm
      simpa [hhalf] using
        (intervalIntegral.integral_comp_sub_left (f := critTime t)
          (a := 0) (b := t / 2) t)
    _ = ∫ s : ℝ in 0..t / 2, critTime t s := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [critTime, sub_sub_cancel_left]
      rw [mul_comm]

/-- Each half of the critical convolution is bounded by `2`. -/
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
      exact mul_le_mul_of_nonneg_right hdec (by
        unfold heatScale12
        exact Real.rpow_nonneg _ _)
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

/-- Uniform critical convolution bound.  In particular the estimate carries
no factor tending to zero with the horizon. -/
theorem critTime_int_le {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in 0..t, critTime t s) ≤ 4 := by
  have hleft := leftCrit_intble ht
  have hhalf : t - t / 2 = t / 2 := by ring
  have hright : IntervalIntegrable (critTime t) volume (t / 2) t := by
    simpa [critTime, hhalf, mul_comm] using hleft.symm.comp_sub_left t
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

/-- A coefficient `K` multiplying the critical flux remains the only small
factor after time integration. -/
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
