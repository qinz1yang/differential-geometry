import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Set.Finite.Range
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter

namespace Filter

universe u v

theorem exists_positive_test_bound_of_pointwise_eventual_bounds
    {W : Type u} {I : ℕ → Type v} (S : Set W)
    (f : ∀ n, I n → ℝ) (test : W → ∀ n, I n → Prop)
    (hfinite : ∀ n, ∃ D : ℝ, ∀ i, f n i ≤ D)
    (htail : ∀ w ∈ S, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ i, test w n i → f n i ≤ B) :
    ∃ A : W → ℝ, (∀ w, 0 < A w) ∧ (∀ w ∉ S, A w = 1) ∧
      ∀ w ∈ S, ∀ n i, test w n i → f n i ≤ A w := by
  classical
  choose D hD using hfinite
  have hex (w : W) : ∃ A : ℝ, 0 < A ∧ (w ∉ S → A = 1) ∧
      (w ∈ S → ∀ n i, test w n i → f n i ≤ A) := by
    by_cases hw : w ∈ S
    · obtain ⟨B, hB⟩ := htail w hw
      obtain ⟨N, hN⟩ := eventually_atTop.mp hB
      obtain ⟨C, hC⟩ := (finite_range (fun j : Fin N => D j)).bddAbove
      let A := 1 + max 0 (max B C)
      have hA : 0 < A := by dsimp [A]; linarith [le_max_left (0 : ℝ) (max B C)]
      refine ⟨A, hA, fun h => (h hw).elim, ?_⟩
      intro _ n i hi
      by_cases hn : N ≤ n
      · exact (hN n hn i hi).trans (by
          have hh := (le_max_left B C).trans (le_max_right 0 (max B C))
          dsimp [A]
          linarith)
      · have hDn : D n ≤ C := hC ⟨⟨n, Nat.lt_of_not_ge hn⟩, rfl⟩
        exact (hD n i).trans (hDn.trans (by
          have hh := (le_max_right B C).trans (le_max_right 0 (max B C))
          dsimp [A]
          linarith))
    · exact ⟨1, zero_lt_one, fun _ => rfl, fun h => (hw h).elim⟩
  choose A hA using hex
  exact ⟨A, fun w => (hA w).1, fun w => (hA w).2.1, fun w => (hA w).2.2⟩

end Filter
