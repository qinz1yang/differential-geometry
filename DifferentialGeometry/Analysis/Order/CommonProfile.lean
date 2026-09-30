import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
noncomputable section
namespace GC.GeneralFlow

def prefixBudget (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => min (1 / 2) (b 0 / 2)
  | n + 1 => min (prefixBudget b n) (b (n + 1) / 2)

theorem prefixBudget_pos {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) (n : ℕ) :
    0 < prefixBudget b n := by
  induction n with
  | zero => exact lt_min (by norm_num) (half_pos (hb 0))
  | succ n ih => exact lt_min ih (half_pos (hb (n + 1)))

theorem prefixBudget_antitone (b : ℕ → ℝ) : Antitone (prefixBudget b) :=
  antitone_nat_of_succ_le fun _ => min_le_left _ _

theorem prefixBudget_le_half (b : ℕ → ℝ) (n : ℕ) : prefixBudget b n ≤ b n / 2 := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n => exact min_le_right _ _

theorem prefixBudget_le_one_half (b : ℕ → ℝ) (n : ℕ) : prefixBudget b n ≤ 1 / 2 :=
  (prefixBudget_antitone b (Nat.zero_le n)).trans (min_le_left _ _)

def commonProfile (b : ℕ → ℝ) (t : ℝ) : ℝ := prefixBudget b (⌊t⌋₊ + 1)

theorem commonProfile_pos {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) (t : ℝ) :
    0 < commonProfile b t := prefixBudget_pos hb _

theorem commonProfile_antitone (b : ℕ → ℝ) : Antitone (commonProfile b) := by
  intro s t hst
  exact prefixBudget_antitone b (Nat.add_le_add_right (Nat.floor_mono hst) 1)

theorem commonProfile_lt_one (b : ℕ → ℝ) (t : ℝ) : commonProfile b t < 1 :=
  lt_of_le_of_lt (prefixBudget_le_one_half b _) (by norm_num)

theorem commonProfile_lt_budget {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (t : ℝ) (n : ℕ) (hn : n ≤ ⌊t⌋₊ + 1) : commonProfile b t < b n := by
  have h := (prefixBudget_antitone b hn).trans (prefixBudget_le_half b n)
  exact lt_of_le_of_lt h (half_lt_self (hb n))

theorem commonProfile_interval_budgets {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    (n : ℕ) (t : ℝ) (ht : (n : ℝ) ≤ t) :
    commonProfile b t < b n ∧ commonProfile b t < b (n + 1) := by
  have hn := Nat.le_floor ht
  exact ⟨commonProfile_lt_budget hb t n (hn.trans (Nat.le_succ _)),
    commonProfile_lt_budget hb t (n + 1) (Nat.succ_le_succ hn)⟩

theorem commonProfile_compact_lower {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) (T : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, t ≤ T → d ≤ commonProfile b t :=
  ⟨commonProfile b T, commonProfile_pos hb T, fun _ ht => commonProfile_antitone b ht⟩

theorem commonProfile_two_registers {b c : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n) :
    ∃ δ : ℝ → ℝ, (∀ t, 0 < δ t) ∧ Antitone δ ∧ (∀ t, δ t < 1) ∧
      ∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t →
        δ t < b n ∧ δ t < c n ∧ δ t < b (n + 1) ∧ δ t < c (n + 1) := by
  let a : ℕ → ℝ := fun n => min (b n) (c n)
  have ha : ∀ n, 0 < a n := fun n => lt_min (hb n) (hc n)
  refine ⟨commonProfile a, commonProfile_pos ha, commonProfile_antitone a,
    commonProfile_lt_one a, ?_⟩
  intro n t ht
  obtain ⟨h₀,h₁⟩ := commonProfile_interval_budgets ha n t ht
  exact ⟨h₀.trans_le (min_le_left _ _), h₀.trans_le (min_le_right _ _),
    h₁.trans_le (min_le_left _ _), h₁.trans_le (min_le_right _ _)⟩

end GC.GeneralFlow
