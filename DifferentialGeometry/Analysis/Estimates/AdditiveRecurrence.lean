import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Estimates

open scoped BigOperators

theorem le_sum_range_of_succ_le_add
    {A : Type*} [AddCommMonoid A] [PartialOrder A] [IsOrderedAddMonoid A]
    {e d : ℕ → A}
    (hzero : e 0 ≤ d 0)
    (hsucc : ∀ k, e (k + 1) ≤ e k + d (k + 1)) :
    ∀ n, e n ≤ ∑ i ∈ Finset.range (n + 1), d i := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        e (n + 1) ≤ e n + d (n + 1) := hsucc n
        _ ≤ (∑ i ∈ Finset.range (n + 1), d i) + d (n + 1) :=
          add_le_add ih (le_refl _)
        _ = ∑ i ∈ Finset.range (n + 1 + 1), d i :=
          (Finset.sum_range_succ d (n + 1)).symm

end DifferentialGeometry.Analysis.Estimates
