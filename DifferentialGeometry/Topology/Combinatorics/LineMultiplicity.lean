import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fin.Basic

namespace Poincare.Topology.Combinatorics

theorem card_le_two_of_pairwise_adjacent (s : Finset ℕ)
    (hs : ∀ i ∈ s, ∀ j ∈ s, i ≤ j + 1) : s.card ≤ 2 := by
  by_cases he : s.Nonempty
  · let m := s.min' he
    have hm : m ∈ s := s.min'_mem he
    have hsub : s ⊆ Finset.Icc m (m + 1) := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, hs i hi m hm⟩
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp

theorem card_fin_le_two_of_pairwise_adjacent {n : ℕ} (s : Finset (Fin n))
    (hs : ∀ i ∈ s, ∀ j ∈ s, i.val ≤ j.val + 1) : s.card ≤ 2 := by
  have h := card_le_two_of_pairwise_adjacent (s.image Fin.val) (by
    intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    exact hs a ha b hb)
  rwa [Finset.card_image_of_injective _ Fin.val_injective] at h

theorem eq_or_adjacent_of_val_le_succ {n : ℕ} (i j : Fin (n + 1))
    (hij : i.val ≤ j.val + 1) (hji : j.val ≤ i.val + 1) :
    i = j ∨ (∃ k : Fin n, i = k.castSucc ∧ j = k.succ) ∨
      (∃ k : Fin n, j = k.castSucc ∧ i = k.succ) := by
  by_cases h : i = j
  · exact Or.inl h
  have hne : i.val ≠ j.val := fun he ↦ h (Fin.ext he)
  by_cases hlt : i.val < j.val
  · have hin : i.val < n := by have hj := j.isLt; omega
    refine Or.inr (Or.inl ⟨⟨i.val, hin⟩, ?_, ?_⟩)
    · exact Fin.ext rfl
    · apply Fin.ext
      change j.val = i.val + 1
      omega
  · have hjn : j.val < n := by have hi := i.isLt; omega
    refine Or.inr (Or.inr ⟨⟨j.val, hjn⟩, ?_, ?_⟩)
    · exact Fin.ext rfl
    · apply Fin.ext
      change i.val = j.val + 1
      omega

end Poincare.Topology.Combinatorics
