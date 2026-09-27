import DifferentialGeometry.Topology.Order.AntitoneSteps
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

namespace WellFoundedLT

theorem exists_forall_ge_of_finite_exceptions
    {α : Type*} [Preorder α] [WellFoundedLT α]
    {f : ℕ → α} {P : ℕ → Prop} {R : Set ℕ} (hR : R.Finite)
    (hmono : ∀ n, n ∉ R → f (n + 1) ≤ f n)
    (hstep : ∀ n, P n ∨ f (n + 1) < f n ∨ n ∈ R) :
    ∃ N : ℕ, ∀ n, N ≤ n → P n := by
  obtain ⟨b, hb⟩ := hR.bddAbove
  have hout (n : ℕ) : b + 1 + n ∉ R := by
    intro hn
    have hbound : b + 1 + n ≤ b := hb hn
    exact (Nat.not_succ_le_self b) ((Nat.le_add_right (b + 1) n).trans hbound)
  have hanti : Antitone (fun n => f (b + 1 + n)) := antitone_nat_of_succ_le (by
    intro n
    simpa only [Nat.add_assoc] using hmono (b + 1 + n) (hout n))
  obtain ⟨N, hN⟩ := hanti.exists_forall_ge_of_or_succ_lt (P := fun n => P (b + 1 + n)) (by
    intro n
    rcases hstep (b + 1 + n) with h | h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [Nat.add_assoc] using h)
    · exact (hout n h).elim)
  refine ⟨b + 1 + N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_assoc] using hN (N + k) (Nat.le_add_right N k)

end WellFoundedLT
