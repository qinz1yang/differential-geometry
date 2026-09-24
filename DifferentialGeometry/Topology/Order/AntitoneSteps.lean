import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Finite.Basic

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

namespace DifferentialGeometry.Topology


theorem exists_eventually_eq_of_antitone_surviving
    {ι : Type*} {alive active : ℕ → Set ι}
    (hfinite : (alive 0).Finite) (halive : Antitone alive)
    (hactive : ∀ n, active n ⊆ alive n)
    (hsurvive : ∀ n, active n ∩ alive (n + 1) ⊆ active (n + 1)) :
    ∃ N : ℕ, ∀ n, N ≤ n → alive n = alive N ∧ active n = active N := by
  have hinactive : Antitone (fun n => alive n \ active n) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    exact ⟨halive (Nat.le_succ n) hx.1, fun h => hx.2 (hsurvive n ⟨h, hx.1⟩)⟩
  let f (n : ℕ) : {s : Set ι // s.Finite} :=
    ⟨alive n, hfinite.subset (halive (Nat.zero_le n))⟩
  let g (n : ℕ) : {s : Set ι // s.Finite} :=
    ⟨alive n \ active n, (f n).property.subset Set.sdiff_subset⟩
  have hf : Antitone f := fun _ _ h => halive h
  have hg : Antitone g := fun _ _ h => hinactive h
  obtain ⟨N₁, hN₁⟩ := WellFoundedLT.antitone_chain_condition hf
  obtain ⟨N₂, hN₂⟩ := WellFoundedLT.antitone_chain_condition hg
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have ha : alive n = alive (max N₁ N₂) :=
    congrArg Subtype.val ((hN₁ n ((le_max_left _ _).trans hn)).symm.trans
      (hN₁ _ (le_max_left _ _)))
  have hi : alive n \ active n = alive (max N₁ N₂) \ active (max N₁ N₂) :=
    congrArg Subtype.val ((hN₂ n ((le_max_right _ _).trans hn)).symm.trans
      (hN₂ _ (le_max_right _ _)))
  refine ⟨ha, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxn
    exact (hi.symm ▸ ⟨ha ▸ hactive n hx, hxn⟩ : x ∈ alive n \ active n).2 hx
  · intro x hx
    by_contra hxn
    exact (hi ▸ ⟨ha.symm ▸ hactive _ hx, hxn⟩ :
      x ∈ alive (max N₁ N₂) \ active (max N₁ N₂)).2 hx


end DifferentialGeometry.Topology
