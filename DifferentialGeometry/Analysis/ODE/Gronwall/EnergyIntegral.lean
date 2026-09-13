import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis.ODE

theorem integral_le_exp_mul_of_hasDerivAt_sub {F L : ℝ → ℝ} {k a b : ℝ} (hk : 0 ≤ k)
    (hab : a ≤ b) (hLcont : ContinuousOn L (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt L (k * L t - F t) t)
    (hFint : IntervalIntegrable F volume a b)
    (hFnn : ∀ t ∈ Icc a b, 0 ≤ F t) (hLb : 0 ≤ L b) :
    (∫ t in a..b, F t) ≤ Real.exp (k * (b - a)) * L a := by
  set W : ℝ → ℝ := fun t => Real.exp (-(k * (t - a))) * L t with hW
  have hexpfun : Continuous fun t : ℝ => Real.exp (-(k * (t - a))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)).neg
  have hmul : IntervalIntegrable (fun t : ℝ => Real.exp (-(k * (t - a))) * F t) volume a b :=
    hFint.continuousOn_mul hexpfun.continuousOn
  have hWcont : ContinuousOn W (Icc a b) := hexpfun.continuousOn.mul hLcont
  have hWderiv : ∀ t ∈ Ioo a b,
      HasDerivAt W (-(Real.exp (-(k * (t - a))) * F t)) t := by
    intro t ht
    have h1 : HasDerivAt (-fun s : ℝ => k * (s - a)) (-k) t := by
      have h : HasDerivAt (fun s : ℝ => k * (s - a)) k t := by
        simpa using HasDerivAt.const_mul k ((hasDerivAt_id t).sub_const a)
      exact h.neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(k * (s - a))))
        (Real.exp (-(k * (t - a))) * (-k)) t := HasDerivAt.exp h1
    have h3 := HasDerivAt.mul h2 (hderiv t ht)
    have hval : Real.exp (-(k * (t - a))) * (-k) * L t +
        Real.exp (-(k * (t - a))) * (k * L t - F t) =
        -(Real.exp (-(k * (t - a))) * F t) := by ring
    rw [hW]
    exact h3.congr_deriv hval
  have hWint : IntervalIntegrable (fun t : ℝ => -(Real.exp (-(k * (t - a))) * F t))
      volume a b := IntervalIntegrable.neg hmul
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hWcont hWderiv hWint
  have hWa : W a = L a := by simp [hW]
  have hWb : 0 ≤ W b := by
    rw [hW]
    exact mul_nonneg (Real.exp_nonneg _) hLb
  have hneg : (∫ t in a..b, Real.exp (-(k * (t - a))) * F t) = L a - W b := by
    have h1 : (∫ t in a..b, -(Real.exp (-(k * (t - a))) * F t)) =
        -(∫ t in a..b, Real.exp (-(k * (t - a))) * F t) :=
      intervalIntegral.integral_neg
    rw [h1, hWa] at hfund
    linarith
  have hkey : (∫ t in a..b, Real.exp (-(k * (t - a))) * F t) ≤ L a := by
    rw [hneg]
    linarith
  have hcmp : Real.exp (-(k * (b - a))) * (∫ t in a..b, F t) ≤
      ∫ t in a..b, Real.exp (-(k * (t - a))) * F t := by
    have hpoint : ∀ t ∈ Icc a b, Real.exp (-(k * (b - a))) * F t ≤
        Real.exp (-(k * (t - a))) * F t := by
      intro t ht
      have hle : -(k * (b - a)) ≤ -(k * (t - a)) := by
        have h1 : k * (t - a) ≤ k * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hk
        linarith
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (hFnn t ht)
    have hleft : IntervalIntegrable (fun t : ℝ => Real.exp (-(k * (b - a))) * F t)
        volume a b := hFint.const_mul _
    have hm := intervalIntegral.integral_mono_on hab hleft hmul hpoint
    rwa [intervalIntegral.integral_const_mul] at hm
  have hmain : Real.exp (-(k * (b - a))) * (∫ t in a..b, F t) ≤ L a := hcmp.trans hkey
  have hmul := mul_le_mul_of_nonneg_left hmain (Real.exp_pos (k * (b - a))).le
  have hsimp : Real.exp (k * (b - a)) *
      (Real.exp (-(k * (b - a))) * (∫ t in a..b, F t)) = ∫ t in a..b, F t := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hsimp] at hmul
  exact hmul

end DifferentialGeometry.Analysis.ODE
