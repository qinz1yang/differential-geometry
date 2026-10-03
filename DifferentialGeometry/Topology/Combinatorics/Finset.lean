import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

section

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem eq_or_eq_of_card_eq_one_of_subset_union {α : Type*} {u w w' : Finset α}
    (hu : u.card = 1) (hw : w.card = 1) (hw' : w'.card = 1)
    (h : (u : Set α) ⊆ (w : Set α) ∪ (w' : Set α)) : u = w ∨ u = w' := by
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hu
  obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hw
  obtain ⟨q', rfl⟩ := Finset.card_eq_one.mp hw'
  have hp := h (Finset.mem_coe.mpr (Finset.mem_singleton_self p))
  simp only [Finset.coe_singleton, mem_union, mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end DifferentialGeometry.Topology.PiecewiseLinear

end

section

open Set

theorem Finset.exists_mem_subset_pair_of_card_le_two {α : Type*} {v : Finset α} (hv : v.card ≤ 2) {x : α}
    (hx : x ∈ v) : ∃ y ∈ v, (v : Set α) ⊆ {x, y} := by
  classical
  by_cases h : ∃ y ∈ v, y ≠ x
  · obtain ⟨y, hy, hyx⟩ := h
    refine ⟨y, hy, fun z hz => ?_⟩
    have hsub : ({x, y} : Finset α) ⊆ v :=
      Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    have heq : ({x, y} : Finset α) = v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hyx.symm]; exact hv)
    rw [← heq] at hz
    simpa using hz
  · push Not at h
    refine ⟨x, hx, fun z hz => ?_⟩
    simp [h z hz]

end
