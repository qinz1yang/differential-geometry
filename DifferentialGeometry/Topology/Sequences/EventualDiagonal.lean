import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Find

namespace Filter

theorem exists_tendsto_atTop_eventually_diagonal {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ᶠ n in atTop, P (j n) n := by
  classical
  choose N hN using fun k => eventually_atTop.mp (h k)
  let j (n : ℕ) := Nat.findGreatest (fun k => N k ≤ n) n
  refine ⟨j, tendsto_atTop_atTop.mpr ?_, ?_⟩
  · intro k
    refine ⟨max (N k) k, fun n hn => ?_⟩
    exact Nat.le_findGreatest ((le_max_right _ _).trans hn)
      ((le_max_left _ _).trans hn)
  · refine eventually_atTop.mpr ⟨N 0, fun n hn => hN (j n) n ?_⟩
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn

end Filter
