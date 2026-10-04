import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false

namespace FILL910
open Set

def prefixKappaMinimum (κ : ℕ → ℝ) : ℕ → ℝ
  | 0 => κ 0
  | n + 1 => min (prefixKappaMinimum κ n) (κ (n + 1))

theorem prefixKappaMinimum_pos (κ : ℕ → ℝ) (hκ : ∀ n, 0 < κ n) (n : ℕ) :
    0 < prefixKappaMinimum κ n := by
  induction n with
  | zero => exact hκ 0
  | succ n ih => exact lt_min ih (hκ (n + 1))

theorem prefixKappaMinimum_le (κ : ℕ → ℝ) (n : ℕ) :
    prefixKappaMinimum κ n ≤ κ n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

theorem prefixKappaMinimum_antitone (κ : ℕ → ℝ) : Antitone (prefixKappaMinimum κ) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

theorem A07_antitone_positive_envelope (κ : ℕ → ℝ) (hκ : ∀ n, 0 < κ n) :
    ∃ κ' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 < κ' t) ∧ AntitoneOn κ' (Ici 0) ∧
      ∀ n : ℕ, κ' n ≤ κ n := by
  refine ⟨fun t => prefixKappaMinimum κ (Nat.ceil t), ?_, ?_, ?_⟩
  · intro t ht
    exact prefixKappaMinimum_pos κ hκ (Nat.ceil t)
  · intro s hs t ht hst
    exact prefixKappaMinimum_antitone κ (Nat.ceil_mono hst)
  · intro n
    simpa using prefixKappaMinimum_le κ n

end FILL910
