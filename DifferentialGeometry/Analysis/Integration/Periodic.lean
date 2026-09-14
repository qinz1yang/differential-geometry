import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory

namespace Function.Periodic

theorem intervalIntegral_le_period {f : ℝ → ℝ} {T a p q : ℝ}
    (hper : Function.Periodic f T) (hint : IntervalIntegrable f volume a (a + T))
    (hnn : ∀ x, 0 ≤ f x) (hqp : q ≤ p + T) :
    (∫ x in p..q, f x) ≤ ∫ x in a..a + T, f x := by
  by_cases hT : T = 0
  · subst T
    simp only [add_zero, intervalIntegral.integral_same] at hqp ⊢
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hqp (fun x _ => hnn x))
  · have hall := hper.intervalIntegrable hT hint
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hall p q) (hall q (p + T))
    have hshift := hper.intervalIntegral_add_eq p a
    have hnonneg : 0 ≤ ∫ x in q..(p + T), f x :=
      intervalIntegral.integral_nonneg hqp (fun x _ => hnn x)
    linarith

end Function.Periodic
