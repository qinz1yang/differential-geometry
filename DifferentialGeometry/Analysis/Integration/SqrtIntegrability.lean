import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open Set MeasureTheory Filter

namespace DifferentialGeometry.Analysis

private theorem sqrt_le_sqrt_mul_rpow {u t A : ℝ} (ht : 0 < t)
    (hbound : t * u ≤ A) :
    Real.sqrt u ≤ Real.sqrt A * t ^ (-(1 / 2 : ℝ)) := by
  calc
    Real.sqrt u ≤ Real.sqrt (A / t) :=
      Real.sqrt_le_sqrt ((le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hbound))
    _ = Real.sqrt A * t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div' A ht.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow,
        div_eq_mul_inv]

private theorem intervalIntegrable_sub_rpow (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - a) ^ (-(1 / 2 : ℝ))) volume a b := by
  simpa only [zero_add, sub_add_cancel] using
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b - a)
      (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_right a

theorem intervalIntegrable_sqrt_of_sub_mul_le {f : ℝ → ℝ} {a b A : ℝ}
    (hab : a ≤ b)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc a b)))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), (t - a) * f t ≤ A) :
    IntervalIntegrable (fun t => Real.sqrt (f t)) volume a b := by
  apply ((intervalIntegrable_sub_rpow a b).const_mul (Real.sqrt A)).mono_fun'
  · rw [uIoc_of_le hab]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hf
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hbound] with t ht hb
    have hpos : 0 < t - a := sub_pos.mpr ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_le_sqrt_mul_rpow hpos hb

theorem integral_sqrt_le_of_sub_mul_le {f : ℝ → ℝ} {a b A : ℝ}
    (hab : a ≤ b)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc a b)))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), (t - a) * f t ≤ A) :
    (∫ t in a..b, Real.sqrt (f t)) ≤ 2 * Real.sqrt A * Real.sqrt (b - a) := by
  have hi := intervalIntegrable_sqrt_of_sub_mul_le hab hf hbound
  have hg := (intervalIntegrable_sub_rpow a b).const_mul (Real.sqrt A)
  have hle : (∫ t in a..b, Real.sqrt (f t)) ≤
      ∫ t in a..b, Real.sqrt A * (t - a) ^ (-(1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply integral_mono_ae hi.1 hg.1
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hbound] with t ht hb
    exact sqrt_le_sqrt_mul_rpow (sub_pos.mpr ht.1) hb
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
      (f := fun t : ℝ => t ^ (-(1 / 2 : ℝ))) a,
    sub_self, integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))] at hle
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero] at hle
  rw [← Real.sqrt_eq_rpow] at hle
  exact hle.trans_eq (by ring)


end DifferentialGeometry.Analysis

end
