import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Finset

theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι X : Type*} [SeminormedAddCommGroup X] (s : Finset ι) (x : ι → X) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  have hsq : ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
    simpa only [sq] using
      mul_self_le_mul_self (norm_nonneg _) (norm_sum_le s x)
  exact hsq.trans sq_sum_le_card_mul_sum_sq

theorem norm_neg_sum_add_sum_sq_le
    {ι κ X : Type*} [SeminormedAddCommGroup X]
    (s : Finset ι) (t : Finset κ) (x : ι → X) (y : κ → X) :
    ‖- (∑ i ∈ s, x i) + (∑ j ∈ t, y j)‖ ^ 2 ≤
      2 * ((s.card : ℝ) + t.card) *
        ((∑ i ∈ s, ‖x i‖ ^ 2) + ∑ j ∈ t, ‖y j‖ ^ 2) := by
  have htri : ‖- (∑ i ∈ s, x i) + (∑ j ∈ t, y j)‖ ≤
      ‖∑ i ∈ s, x i‖ + ‖∑ j ∈ t, y j‖ := by
    simpa only [norm_neg] using
      norm_add_le (- (∑ i ∈ s, x i)) (∑ j ∈ t, y j)
  have hsq : ‖- (∑ i ∈ s, x i) + (∑ j ∈ t, y j)‖ ^ 2 ≤
      (‖∑ i ∈ s, x i‖ + ‖∑ j ∈ t, y j‖) ^ 2 := by
    simpa only [sq] using mul_self_le_mul_self (norm_nonneg _) htri
  have hsplit : ‖- (∑ i ∈ s, x i) + (∑ j ∈ t, y j)‖ ^ 2 ≤
      2 * (‖∑ i ∈ s, x i‖ ^ 2 + ‖∑ j ∈ t, y j‖ ^ 2) := by
    nlinarith [sq_nonneg (‖∑ i ∈ s, x i‖ - ‖∑ j ∈ t, y j‖)]
  have hx := norm_sum_sq_le_card_mul_sum_norm_sq s x
  have hy := norm_sum_sq_le_card_mul_sum_norm_sq t y
  have hs : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ t.card := Nat.cast_nonneg _
  have hxsum : 0 ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hysum : 0 ≤ ∑ j ∈ t, ‖y j‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_nonneg hs hysum, mul_nonneg ht hxsum]

end Finset
