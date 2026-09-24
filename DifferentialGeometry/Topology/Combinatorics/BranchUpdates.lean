import Mathlib.Data.Nat.Nth
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

namespace DifferentialGeometry.Topology

theorem eq_of_no_update_between
    {ι X : Type*} (label : ℕ → ι) (state : ℕ → ι → X)
    (hunchanged : ∀ n i, label n ≠ i → state (n + 1) i = state n i)
    (i : ι) {a b : ℕ} (hab : a ≤ b)
    (hgap : ∀ m, a ≤ m → m < b → label m ≠ i) : state b i = state a i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : state (a + k) i = state a i :=
      ih (by omega) (fun m hm hmk => hgap m hm (by omega))
    calc
      state (a + (k + 1)) i = state (a + k + 1) i := by rw [Nat.add_assoc]
      _ = state (a + k) i := hunchanged (a + k) i (hgap _ (by omega) (by omega))
      _ = _ := hk

theorem state_succ_eq_of_consecutive_occurrences
    {ι X : Type*} (label : ℕ → ι) (state : ℕ → ι → X)
    (hunchanged : ∀ n i, label n ≠ i → state (n + 1) i = state n i)
    (i : ι) (s : ℕ → ℕ) (hmono : StrictMono s)
    (hgap : ∀ n m, s n < m → m < s (n + 1) → label m ≠ i) (n : ℕ) :
    state (s (n + 1)) i = state (s n + 1) i :=
  eq_of_no_update_between label state hunchanged i (Nat.succ_le_of_lt (hmono (Nat.lt_succ_self n)))
    (fun m hm hmn => hgap n m (by omega) hmn)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

theorem exists_strictMono_event_subsequence {X : Type*} {event : ℕ → Prop}
    (hinfinite : {n | event n}.Infinite) (state : ℕ → X)
    (hunchanged : ∀ n, ¬ event n → state (n + 1) = state n) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, event (s n)) ∧
      (∀ m, event m ↔ ∃ n, s n = m) ∧
      (∀ m, m < s 0 → ¬ event m) ∧
      (∀ n m, s n < m → m < s (n + 1) → ¬ event m) ∧
      state (s 0) = state 0 ∧
      ∀ n, state (s (n + 1)) = state (s n + 1) := by
  have hconstant {a b : ℕ} (hab : a ≤ b)
      (hgap : ∀ m, a ≤ m → m < b → ¬ event m) : state b = state a := by
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih =>
      exact (hunchanged b (hgap b hab (Nat.lt_succ_self b))).trans
        (ih fun m ham hmb => hgap m ham (hmb.trans (Nat.lt_succ_self b)))
  let s := Nat.nth event
  have hmono : StrictMono s := Nat.nth_strictMono hinfinite
  have hmem (n : ℕ) : event (s n) := Nat.nth_mem_of_infinite hinfinite n
  have hcover (m : ℕ) : event m ↔ ∃ n, s n = m := by
    change m ∈ Set.ofPred event ↔ m ∈ Set.range s
    rw [Nat.range_nth_of_infinite hinfinite]
  have hbefore (m : ℕ) (hm : m < s 0) : ¬ event m := by
    intro hevent
    obtain ⟨n, rfl⟩ := (hcover m).mp hevent
    exact hm.not_ge (hmono.monotone (Nat.zero_le n))
  have hgap (n m : ℕ) (hnm : s n < m) (hms : m < s (n + 1)) : ¬ event m := by
    intro hevent
    exact hnm.not_ge (Nat.le_nth_of_lt_nth_succ hms hevent)
  refine ⟨s, hmono, hmem, hcover, hbefore, hgap, ?_, ?_⟩
  · exact hconstant (Nat.zero_le _) (fun m _ hm => hbefore m hm)
  · intro n
    exact hconstant (Nat.succ_le_of_lt (hmono (Nat.lt_succ_self n)))
      (fun m hm hmn => hgap n m (Nat.lt_of_succ_le hm) hmn)

end DifferentialGeometry.Topology
