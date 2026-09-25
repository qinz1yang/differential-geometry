import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fin.Basic

namespace Fin

private theorem exists_fixed_between_of_noncrossing {n : ℕ} {σ : Fin n → Fin n}
    (hinv : Function.Involutive σ)
    (hnc : ∀ a b, a < b → b < σ a → σ a < σ b → False)
    (hno : ∀ a, (σ a).val ≠ a.val + 1) {a b : Fin n} (hab : a < b) (hp : σ a = b) :
    ∃ k, a < k ∧ k < b ∧ σ k = k := by
  have aux : ∀ m, ∀ a b : Fin n, b.val = m → a < b → σ a = b →
      ∃ k, a < k ∧ k < b ∧ σ k = k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b hbm hab hp
      have hgap := hno a
      rw [hp] at hgap
      have hsucc : a.val + 1 < b.val := by omega
      let c : Fin n := ⟨a.val + 1, lt_trans hsucc b.isLt⟩
      have hac : a < c := by change a.val < a.val + 1; omega
      have hcb : c < b := hsucc
      by_cases hfix : σ c = c
      · exact ⟨c, hac, hcb, hfix⟩
      have hσca : σ c ≠ a := by
        intro heq
        have h := congrArg σ heq
        rw [hinv c, hp] at h
        exact (ne_of_lt hcb) h
      have hσcb : σ c ≠ b := by
        intro heq
        have h := hinv.injective (heq.trans hp.symm)
        exact (ne_of_gt hac) h
      have haσc : a < σ c := by
        by_contra hnot
        have hlt : σ c < a := lt_of_le_of_ne (le_of_not_gt hnot) hσca
        have h := hnc (σ c) a hlt
        rw [hinv c, hp] at h
        exact h hac hcb
      have hσcb' : σ c < b := by
        by_contra hnot
        have hlt : b < σ c := lt_of_le_of_ne (le_of_not_gt hnot) hσcb.symm
        exact hnc a c hac (hp ▸ hcb) (hp ▸ hlt)
      rcases lt_or_gt_of_ne hfix with hleft | hright
      · obtain ⟨k, hck, hkc, hk⟩ := ih c.val (by omega) (σ c) c rfl hleft (hinv c)
        exact ⟨k, haσc.trans hck, hkc.trans hcb, hk⟩
      · obtain ⟨k, hck, hkc, hk⟩ :=
          ih (σ c).val (by omega) c (σ c) rfl hright rfl
        exact ⟨k, hac.trans hck, hkc.trans hσcb', hk⟩
  exact aux b.val a b rfl hab hp

theorem strictAnti_of_noncrossing_involution_without_adjacent_pairs
    {n : ℕ} {σ : Fin n → Fin n} (hinv : Function.Involutive σ)
    (hnc : ∀ a b, a < b → b < σ a → σ a < σ b → False)
    (hunique : ∀ a b, σ a = a → σ b = b → a = b)
    (hno : ∀ a, (σ a).val ≠ a.val + 1) : StrictAnti σ := by
  have hcenter (a : Fin n) : ∃ k, σ k = k ∧
      ((a = k ∧ σ a = k) ∨ (a < k ∧ k < σ a) ∨ (σ a < k ∧ k < a)) := by
    rcases lt_trichotomy a (σ a) with hlt | heq | hgt
    · obtain ⟨k, hak, hkσ, hk⟩ :=
        exists_fixed_between_of_noncrossing hinv hnc hno hlt rfl
      exact ⟨k, hk, Or.inr (Or.inl ⟨hak, hkσ⟩)⟩
    · exact ⟨a, heq.symm, Or.inl ⟨rfl, heq.symm⟩⟩
    · obtain ⟨k, hσk, hka, hk⟩ :=
        exists_fixed_between_of_noncrossing hinv hnc hno hgt (hinv a)
      exact ⟨k, hk, Or.inr (Or.inr ⟨hσk, hka⟩)⟩
  intro a b hab
  by_contra hnot
  have hne : σ a ≠ σ b := fun h => (ne_of_lt hab) (hinv.injective h)
  have hσ : σ a < σ b := lt_of_le_of_ne (le_of_not_gt hnot) hne
  obtain ⟨k, hk, hak⟩ := hcenter a
  obtain ⟨l, hl, hbl⟩ := hcenter b
  have hkl := hunique k l hk hl
  subst l
  have hnc₁ := hnc a b hab
  have hnc₂ := hnc (σ a) (σ b) hσ
  rw [hinv a, hinv b] at hnc₂
  have hn₁ : ¬ b < σ a := fun h => hnc₁ h hσ
  have hn₂ : ¬ σ b < a := fun h => hnc₂ h hab
  rcases hak with ⟨ha, hσa⟩ | ⟨hak, hkσa⟩ | ⟨hσak, hka⟩ <;>
    rcases hbl with ⟨hb, hσb⟩ | ⟨hbk, hkσb⟩ | ⟨hσbk, hkb⟩ <;> omega

theorem exists_adjacent_pair_of_distinct_noncrossing_involutions
    {n : ℕ} {σ τ : Fin n → Fin n}
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (hσnc : ∀ a b, a < b → b < σ a → σ a < σ b → False)
    (hτnc : ∀ a b, a < b → b < τ a → τ a < τ b → False)
    (hσunique : ∀ a b, σ a = a → σ b = b → a = b)
    (hτunique : ∀ a b, τ a = a → τ b = b → a = b) (hne : σ ≠ τ) :
    ∃ a, (σ a).val = a.val + 1 ∨ (τ a).val = a.val + 1 := by
  by_contra hnot
  have hσno : ∀ a, (σ a).val ≠ a.val + 1 := fun a h => hnot ⟨a, Or.inl h⟩
  have hτno : ∀ a, (τ a).val ≠ a.val + 1 := fun a h => hnot ⟨a, Or.inr h⟩
  have hσanti := strictAnti_of_noncrossing_involution_without_adjacent_pairs
    hσ hσnc hσunique hσno
  have hτanti := strictAnti_of_noncrossing_involution_without_adjacent_pairs
    hτ hτnc hτunique hτno
  have hid := (hσanti.comp hτanti).eq_id
  apply hne
  funext a
  have h := congrArg σ (congrFun hid a)
  simpa only [Function.comp_apply, id_eq, hσ (τ a)] using h.symm

theorem exists_adjacent_pair_of_fixed_point_free_noncrossing_involution
    {n : ℕ} (hn : 0 < n) {σ : Fin n → Fin n} (hinv : Function.Involutive σ)
    (hnc : ∀ a b, a < b → b < σ a → σ a < σ b → False)
    (hfree : ∀ a, σ a ≠ a) : ∃ a, (σ a).val = a.val + 1 := by
  by_contra hnot
  have hno : ∀ a, (σ a).val ≠ a.val + 1 := fun a h => hnot ⟨a, h⟩
  let a : Fin n := ⟨0, hn⟩
  have hlt : a < σ a := by
    have hne := hfree a
    have hval : (σ a).val ≠ 0 := fun h => hne (Fin.ext h)
    change 0 < (σ a).val
    omega
  obtain ⟨k, -, -, hk⟩ := exists_fixed_between_of_noncrossing hinv hnc hno hlt rfl
  exact hfree k hk

end Fin
