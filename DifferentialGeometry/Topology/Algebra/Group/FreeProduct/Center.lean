import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Commutative

/-!
# Central elements of free products

A free product with two distinct nontrivial factors has trivial centre. The proof compares the
first letters of the reduced words of `g * z` and `z * g` for a suitable letter `g`. Consequently
a group with a nontrivial central element is freely indecomposable.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace GC.Group

open Monoid.CoprodI

private theorem neWord_fstIdx_toWord {ι : Type u} {M : ι → Type v} [∀ i, Monoid (M i)]
    {i j : ι} (w : NeWord M i j) : w.toWord.fstIdx = some i := by
  change w.toList.head?.map Sigma.fst = some i
  simp

private theorem neWord_index_eq_of_prod_eq {ι : Type u} {M : ι → Type v} [∀ i, Monoid (M i)]
    {i j k l : ι} (w₁ : NeWord M i j) (w₂ : NeWord M k l) (h : w₁.prod = w₂.prod) : i = k := by
  classical
  have hw : w₁.toWord = w₂.toWord := (Word.equiv (M := M)).symm.injective h
  have hf := congrArg Word.fstIdx hw
  rw [neWord_fstIdx_toWord, neWord_fstIdx_toWord] at hf
  exact Option.some.inj hf

theorem coprodI_eq_one_of_forall_commute {ι : Type u} (M : ι → Type v) [∀ i, Group (M i)]
    {i j : ι} (hij : i ≠ j) (hi : Nontrivial (M i)) (hj : Nontrivial (M j))
    (z : Monoid.CoprodI M) (hz : ∀ x, x * z = z * x) : z = 1 := by
  classical
  by_contra hz1
  have hw : Word.equiv z ≠ Word.empty := by
    intro h
    apply hz1
    rw [← (Word.equiv (M := M)).symm_apply_apply z, h]
    rfl
  obtain ⟨a, b, w, hwz⟩ := NeWord.of_word (Word.equiv z) hw
  have hzw : w.prod = z := by
    change w.toWord.prod = z
    rw [hwz]
    exact (Word.equiv (M := M)).symm_apply_apply z
  by_cases hab : a = b
  · subst hab
    obtain ⟨k, hk, x, hx⟩ : ∃ k, k ≠ a ∧ ∃ x : M k, x ≠ 1 := by
      by_cases hia : i = a
      · subst hia
        exact ⟨j, hij.symm, exists_ne 1⟩
      · exact ⟨i, hia, exists_ne 1⟩
    have h1 : (NeWord.append (NeWord.singleton x hx) hk w).prod =
        (NeWord.append w hk.symm (NeWord.singleton x hx)).prod := by
      rw [NeWord.append_prod, NeWord.append_prod, NeWord.prod_singleton, hzw]
      exact hz (of x)
    exact hk (neWord_index_eq_of_prod_eq _ _ h1)
  · let p := Word.equivPair a (Word.equiv z)
    have hf := p.fstIdx_ne
    have ht : p.tail.prod = of p.head⁻¹ * z := by
      change (Word.equivPair a (Word.equiv z)).tail.prod = _
      rw [Word.equivPair_tail_eq_inv_smul, Word.prod_smul, map_inv]
      congr 1
      exact (Word.equiv (M := M)).symm_apply_apply z
    by_cases hp : p.head = 1
    · have he : p.tail = w.toWord := by
        apply (Word.equiv (M := M)).symm.injective
        change p.tail.prod = w.prod
        rw [ht, hp, inv_one, map_one, one_mul, hzw]
      rw [he, neWord_fstIdx_toWord] at hf
      exact hf rfl
    · have hq : p.head⁻¹ ≠ 1 := inv_ne_one.mpr hp
      have he : p.tail = (NeWord.append w (Ne.symm hab) (NeWord.singleton _ hq)).toWord := by
        apply (Word.equiv (M := M)).symm.injective
        change p.tail.prod = (NeWord.append w (Ne.symm hab) (NeWord.singleton _ hq)).prod
        rw [ht, NeWord.append_prod, NeWord.prod_singleton, hzw]
        exact hz _
      rw [he, neWord_fstIdx_toWord] at hf
      exact hf rfl

theorem subsingleton_factor_of_center_nontrivial (G : Type u) (H : Type v) [Group G] [Group H]
    (z : Monoid.Coprod G H) (hz : z ≠ 1) (hc : ∀ x, x * z = z * x) :
    Subsingleton G ∨ Subsingleton H := by
  by_contra h
  have hG : ¬ Subsingleton G := fun hs => h (Or.inl hs)
  have hH : ¬ Subsingleton H := fun hs => h (Or.inr hs)
  let M := DifferentialGeometry.Algebra.Group.boolCoprodFamily G H
  let e := DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod G H
  have hM : ∀ b : Bool, Nontrivial (M b) := by
    intro b
    cases b
    · let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hG
      exact inferInstanceAs (Nontrivial (ULift G))
    · let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
      exact inferInstanceAs (Nontrivial (ULift H))
  apply hz
  have h1 : e.symm z = 1 := by
    apply coprodI_eq_one_of_forall_commute M Bool.false_ne_true (hM false) (hM true)
    intro x
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hc (e x)
  simpa only [map_one, MulEquiv.apply_symm_apply] using congrArg e h1

theorem freelyIndecomposable_of_center_nontrivial (G : Type u) [Group G] (z : G) (hz : z ≠ 1)
    (hc : ∀ x : G, x * z = z * x) : FreelyIndecomposable G := by
  intro A B _ _ he
  obtain ⟨e⟩ := he
  apply subsingleton_factor_of_center_nontrivial A B (e z)
  · intro h
    apply hz
    simpa only [map_one, MulEquiv.symm_apply_apply] using congrArg e.symm h
  · intro x
    apply e.symm.injective
    simpa only [map_mul, MulEquiv.symm_apply_apply] using hc (e.symm x)

end GC.Group
