import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace Real.smoothTransition

theorem one_sub (x : ℝ) : smoothTransition (1 - x) = 1 - smoothTransition x := by
  unfold smoothTransition
  have hden := (pos_denom x).ne'
  rw [sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x))]
  field_simp
  ring

theorem integral_zero_one : (∫ x in (0 : ℝ)..1, smoothTransition x) = 1 / 2 := by
  have hcont : IntervalIntegrable smoothTransition MeasureTheory.volume 0 1 :=
    smoothTransition.continuous.intervalIntegrable 0 1
  have hchange :
      (∫ x in (0 : ℝ)..1, smoothTransition (1 - x)) =
        ∫ x in (0 : ℝ)..1, smoothTransition x := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := smoothTransition) (a := (0 : ℝ)) (b := 1) 1)
  simp_rw [one_sub] at hchange
  rw [intervalIntegral.integral_sub intervalIntegrable_const hcont] at hchange
  norm_num at hchange ⊢
  linarith

theorem integral_comp_sub_div (a b : ℝ) :
    (∫ x in a..b, smoothTransition ((x - a) / (b - a))) = (b - a) / 2 := by
  by_cases hab : b = a
  · subst b
    simp
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => smoothTransition (x / (b - a))) a]
    rw [intervalIntegral.integral_comp_div smoothTransition hba]
    simp only [sub_self, zero_div, div_self hba, integral_zero_one, smul_eq_mul]
    ring

end Real.smoothTransition
