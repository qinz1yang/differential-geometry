import Mathlib.GroupTheory.CoprodI

/-!
# First letters in free products

Tier T4a of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §1, T4.2).
`firstIdx g` is the index of the first letter of the reduced word of `g` in `Monoid.CoprodI M`.

* Left multiplication by a nontrivial letter of a different factor prepends it
  (`firstIdx_of_mul`).
* Right multiplication by a letter changes the first letter only of `1` and of the inverse letter
  (`firstIdx_mul_of`): a reduced word of length at least two keeps its first letter, and a
  one-letter word either keeps its index or cancels.
* Hence, for any predicate `P` on first indices, the set `{g | P (firstIdx g)}` is almost
  invariant under right multiplication: it changes on finitely many elements for each `s`
  (`finite_setOf_firstIdx_mul_ne`), and it is invariant under the factor `k` when `P none ↔
  P (some k)` (`firstIdx_mul_of_iff`).
* For two nontrivial factors indexed by `Bool`, the set of elements not starting with a letter of
  `M false` and its complement are both infinite unless the free product is finite
  (`finite_of_finite_setOf_firstIdx_ne`).
-/

set_option autoImplicit false

noncomputable section

open Monoid.CoprodI

namespace GC.Group.FirstLetter

variable {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)] [DecidableEq ι] [∀ i, DecidableEq (M i)]

def firstIdx (g : Monoid.CoprodI M) : Option ι :=
  (Word.equiv g).fstIdx

theorem word_equiv_mul (g h : Monoid.CoprodI M) :
    Word.equiv (g * h) = g • Word.equiv h := by
  change (g * h) • (Word.empty : Word M) = g • (h • Word.empty)
  exact mul_smul g h _

theorem word_equiv_symm (w : Word M) : Word.equiv.symm w = w.prod :=
  rfl

theorem firstIdx_one : firstIdx (1 : Monoid.CoprodI M) = none := by
  unfold firstIdx
  have h : Word.equiv (1 : Monoid.CoprodI M) = Word.empty := by
    change (1 : Monoid.CoprodI M) • (Word.empty : Word M) = _
    exact one_smul _ _
  rw [h]
  rfl

theorem firstIdx_eq_none_iff (g : Monoid.CoprodI M) : firstIdx g = none ↔ g = 1 := by
  constructor
  · intro h
    have hw : Word.equiv g = Word.empty := by
      apply Word.ext
      unfold firstIdx Word.fstIdx at h
      simpa using h
    rw [← Word.equiv.symm_apply_apply g, hw]
    rfl
  · rintro rfl
    exact firstIdx_one

theorem firstIdx_of_mul {i : ι} (x : M i) (hx : x ≠ 1) (g : Monoid.CoprodI M)
    (hg : firstIdx g ≠ some i) : firstIdx (of x * g) = some i := by
  have hg' : (Word.equiv g).fstIdx ≠ some i := hg
  unfold firstIdx
  rw [word_equiv_mul, ← Word.cons_eq_smul (h1 := hg') (h2 := hx)]
  exact Word.fstIdx_cons _ _ _ _

theorem firstIdx_of {i : ι} (x : M i) (hx : x ≠ 1) :
    firstIdx (of x : Monoid.CoprodI M) = some i := by
  have h := firstIdx_of_mul x hx 1 (by rw [firstIdx_one]; simp)
  rwa [mul_one] at h

theorem firstIdx_of_eq (i : ι) (x : M i) :
    firstIdx (of x : Monoid.CoprodI M) = none ∨ firstIdx (of x : Monoid.CoprodI M) = some i := by
  by_cases hx : x = 1
  · left
    rw [hx, map_one, firstIdx_one]
  · exact Or.inr (firstIdx_of x hx)

private theorem fstIdx_mul_of {k : ι} (x : M k) :
    ∀ w : Word M, w.prod ≠ 1 → w.prod * of x ≠ 1 →
      firstIdx (w.prod * of x) = w.fstIdx := by
  intro w
  induction w using Word.consRecOn with
  | empty =>
    intro h
    exact absurd rfl h
  | cons j y tail h1 h2 ih =>
    intro _ hne
    rw [Word.prod_cons, Word.fstIdx_cons]
    rw [Word.prod_cons] at hne
    by_cases ht : tail.prod = 1
    · rw [ht, mul_one] at hne ⊢
      by_cases hkj : k = j
      · subst hkj
        rw [← map_mul] at hne ⊢
        have hyx : y * x ≠ 1 := fun h => hne (by rw [h, map_one])
        exact firstIdx_of _ hyx
      · apply firstIdx_of_mul y h2
        rcases firstIdx_of_eq k x with h | h
        · rw [h]
          simp
        · rw [h]
          exact fun he => hkj (Option.some.inj he)
    · rw [mul_assoc]
      apply firstIdx_of_mul y h2
      by_cases htx : tail.prod * of x = 1
      · rw [htx, firstIdx_one]
        simp
      · rw [ih ht htx]
        exact h1

theorem firstIdx_mul_of {k : ι} (g : Monoid.CoprodI M) (x : M k) (hg : g ≠ 1)
    (hgx : g * of x ≠ 1) : firstIdx (g * of x) = firstIdx g := by
  have h := fstIdx_mul_of x (Word.equiv g)
  rw [← word_equiv_symm, Word.equiv.symm_apply_apply] at h
  exact h hg hgx

theorem firstIdx_mul_of_iff (P : Option ι → Prop) {k : ι} (hP : P none ↔ P (some k))
    (g : Monoid.CoprodI M) (x : M k) : P (firstIdx (g * of x)) ↔ P (firstIdx g) := by
  have hof : ∀ y : M k, P (firstIdx (of y : Monoid.CoprodI M)) ↔ P none := by
    intro y
    rcases firstIdx_of_eq k y with h | h
    · rw [h]
    · rw [h]
      exact hP.symm
  by_cases hg : g = 1
  · rw [hg, one_mul, hof, firstIdx_one]
  by_cases hgx : g * of x = 1
  · have hg' : g = of x⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hgx
    rw [hgx, firstIdx_one, hg', hof]
  rw [firstIdx_mul_of g x hg hgx]

theorem setOf_firstIdx_mul_of_ne_subset (P : Option ι → Prop) {k : ι} (x : M k) :
    {g : Monoid.CoprodI M | ¬ (P (firstIdx (g * of x)) ↔ P (firstIdx g))} ⊆
      {1, (of x)⁻¹} := by
  intro g hg
  by_contra hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  apply hg
  have hgx : g * of x ≠ 1 := fun h => hmem.2 (eq_inv_of_mul_eq_one_left h)
  rw [firstIdx_mul_of g x hmem.1 hgx]

theorem finite_setOf_firstIdx_mul_ne (P : Option ι → Prop) (s : Monoid.CoprodI M) :
    {g : Monoid.CoprodI M | ¬ (P (firstIdx (g * s)) ↔ P (firstIdx g))}.Finite := by
  induction s using Monoid.CoprodI.induction_on with
  | one => simp
  | of _ x =>
    exact ((Set.finite_singleton ((of x)⁻¹ : Monoid.CoprodI M)).insert 1).subset
      (setOf_firstIdx_mul_of_ne_subset P x)
  | mul a b ha hb =>
    have himg : ((fun g => g * a⁻¹) ''
        {g : Monoid.CoprodI M | ¬ (P (firstIdx (g * b)) ↔ P (firstIdx g))}).Finite :=
      hb.image _
    apply (ha.union himg).subset
    intro g hg
    by_cases hga : P (firstIdx (g * a)) ↔ P (firstIdx g)
    · right
      refine ⟨g * a, ?_, mul_inv_cancel_right g a⟩
      intro hab
      apply hg
      rw [← mul_assoc]
      exact hab.trans hga
    · exact Or.inl hga

end GC.Group.FirstLetter

namespace GC.Group.FirstLetter

variable {M : Bool → Type*} [∀ i, Group (M i)] [∀ i, DecidableEq (M i)]

theorem finite_of_finite_setOf_firstIdx_ne (a : M true) (ha : a ≠ 1) (b : M false) (hb : b ≠ 1)
    (h : {g : Monoid.CoprodI M | firstIdx g ≠ some false}.Finite ∨
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}ᶜ.Finite) :
    Finite (Monoid.CoprodI M) := by
  have hA : Set.MapsTo (fun g => of a * g)
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}ᶜ
      {g : Monoid.CoprodI M | firstIdx g ≠ some false} := by
    intro g hg
    have hg' : firstIdx g = some false := not_not.mp hg
    have hne : firstIdx g ≠ some true := by rw [hg']; simp
    change firstIdx (of a * g) ≠ some false
    rw [firstIdx_of_mul a ha g hne]
    simp
  have hB : Set.MapsTo (fun g => of b * g)
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}ᶜ := by
    intro g hg
    have hg' : firstIdx g ≠ some false := hg
    change ¬ firstIdx (of b * g) ≠ some false
    rw [firstIdx_of_mul b hb g hg']
    simp
  have hinjA : Set.InjOn (fun g : Monoid.CoprodI M => of a * g)
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}ᶜ :=
    fun _ _ _ _ h => mul_left_cancel h
  have hinjB : Set.InjOn (fun g : Monoid.CoprodI M => of b * g)
      {g : Monoid.CoprodI M | firstIdx g ≠ some false} :=
    fun _ _ _ _ h => mul_left_cancel h
  have hboth : {g : Monoid.CoprodI M | firstIdx g ≠ some false}.Finite ∧
      {g : Monoid.CoprodI M | firstIdx g ≠ some false}ᶜ.Finite := by
    rcases h with h | h
    · exact ⟨h, Set.Finite.of_finite_image (h.subset hA.image_subset) hinjA⟩
    · exact ⟨Set.Finite.of_finite_image (h.subset hB.image_subset) hinjB, h⟩
  have huniv : (Set.univ : Set (Monoid.CoprodI M)).Finite := by
    rw [← Set.union_compl_self {g : Monoid.CoprodI M | firstIdx g ≠ some false}]
    exact hboth.1.union hboth.2
  exact Set.finite_univ_iff.mp huniv

end GC.Group.FirstLetter
