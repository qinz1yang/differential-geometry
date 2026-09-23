import Mathlib.Order.OrderIsoNat

set_option autoImplicit false

namespace Antitone

variable {α : Type*} [Preorder α] [WellFoundedLT α]

theorem exists_forall_ge_of_or_succ_lt {f : ℕ → α} (hf : Antitone f)
    {P : ℕ → Prop} (hstep : ∀ n, P n ∨ f (n + 1) < f n) :
    ∃ N : ℕ, ∀ n, N ≤ n → P n := by
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition'
    (α := OrderDual α) (⟨f, hf⟩ : ℕ →o OrderDual α)
  refine ⟨N, ?_⟩
  intro n hn
  rcases hstep n with h | h
  · exact h
  · have hbad : f (n + 1) < f N := h.trans_le (hf hn)
    exact (hN (n + 1) (hn.trans (Nat.le_succ n)) hbad).elim

end Antitone
