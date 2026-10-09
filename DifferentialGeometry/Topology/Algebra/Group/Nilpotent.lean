import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Subgroup.Centralizer

open scoped commutatorElement

namespace Subgroup

variable {H : Type*} [Group H]

private theorem mem_upperCentralSeries_of_iterated_commutator_eq_one
    (S : Set H) (hS : closure S = ⊤) (n : ℕ) (x : H)
    (h : ∀ l : List H, l.length = n → (∀ t ∈ l, t ∈ S) →
      l.foldl (fun c t => ⁅c, t⁆) x = 1) : x ∈ upperCentralSeries H n := by
  induction n generalizing x with
  | zero =>
    have hx := h [] rfl (by simp)
    simpa only [upperCentralSeries_zero, mem_bot, List.foldl_nil] using hx
  | succ n ih =>
    apply mem_upperCentralSeries_succ_iff.mpr
    let N := upperCentralSeries H n
    let q := QuotientGroup.mk' N
    have hgen (y : H) (hy : y ∈ S) : ⁅x, y⁆ ∈ N := by
      apply ih
      intro l hl hmem
      exact h (y :: l) (by simp only [List.length_cons, hl]) (by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hy
        · exact hmem t ht)
    have hC : closure S ≤ (centralizer {q x}).comap q := by
      apply (closure_le _).mpr
      intro y hy
      apply mem_centralizer_iff_commutator_eq_one.mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hgen y hy)
    intro y
    have hyC : q y ∈ centralizer {q x} := hC (by rw [hS]; exact mem_top y)
    have heq := (mem_centralizer_iff_commutator_eq_one.mp hyC) (q x) (Set.mem_singleton _)
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact heq

theorem isNilpotent_closure_of_iterated_commutator_eq_one (S : Set H) (n : ℕ)
    (h : ∀ s ∈ S, ∀ l : List H, l.length = n → (∀ t ∈ l, t ∈ S) →
      l.foldl (fun c t => ⁅c, t⁆) s = 1) : Group.IsNilpotent (closure S) := by
  let T : Set (closure S) := Subtype.val ⁻¹' S
  have hT : closure T = ⊤ := closure_closure_coe_preimage
  have hgen : T ⊆ upperCentralSeries (closure S) n := by
    intro s hs
    apply mem_upperCentralSeries_of_iterated_commutator_eq_one T hT n s
    intro l hl hmem
    apply Subtype.ext
    have hm : ∀ t ∈ l.map Subtype.val, t ∈ S := by
      intro t ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      exact hmem y hy
    have heq := h s hs (l.map Subtype.val) (by simpa only [List.length_map] using hl) hm
    rw [List.foldl_map_hom (f := fun c t : closure S => ⁅c, t⁆) (fun _ _ => rfl)] at heq
    exact heq
  exact ⟨n, top_unique (hT ▸ (closure_le _).mpr hgen)⟩

end Subgroup
