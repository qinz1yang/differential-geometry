import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Finite
set_option autoImplicit false
noncomputable section
universe u v w
namespace GC.Group
open Monoid.CoprodI

theorem exists_pairWord {ι : Type u} (M : ι → Type v) [∀ i, Monoid (M i)]
    {i j : ι} (hij : i ≠ j) (a : M i) (ha : a ≠ 1) (b : M j) (hb : b ≠ 1) :
    ∀ n : ℕ, ∃ z : Word M, z.fstIdx ≠ some j ∧ z.toList.length = 2 * n := by
  intro n
  induction n with
  | zero => exact ⟨Word.empty, by simp [Word.fstIdx, Word.empty], rfl⟩
  | succ n ih =>
      obtain ⟨z, hz, hlen⟩ := ih
      let t := Word.cons b z hz hb
      have ht : t.fstIdx ≠ some i := by simp [t, Ne.symm hij]
      refine ⟨Word.cons a t ht ha, ?_, ?_⟩
      · simpa only [Word.fstIdx_cons, ne_eq, Option.some.injEq] using hij
      · simp only [Word.cons_toList, List.length_cons, t, hlen]
        omega

theorem infinite_coprodI_of_two_factors {ι : Type u} (M : ι → Type v)
    [∀ i, Monoid (M i)] {i j : ι} (hij : i ≠ j)
    (a : M i) (ha : a ≠ 1) (b : M j) (hb : b ≠ 1) : Infinite (Monoid.CoprodI M) := by
  classical
  let z : ℕ → Word M := fun n => Classical.choose (exists_pairWord M hij a ha b hb n)
  have hz : Function.Injective z := by
    intro m n h
    have hh := congrArg (fun w : Word M => w.toList.length) h
    have hm := (Classical.choose_spec (exists_pairWord M hij a ha b hb m)).2
    have hn := (Classical.choose_spec (exists_pairWord M hij a ha b hb n)).2
    change (z m).toList.length = 2 * m at hm
    change (z n).toList.length = 2 * n at hn
    omega
  exact Infinite.of_injective ((Word.equiv (M := M)).symm ∘ z)
    ((Word.equiv (M := M)).symm.injective.comp hz)

theorem infinite_coprod (G : Type u) (H : Type v) [Group G] [Group H]
    [Nontrivial G] [Nontrivial H] : Infinite (Monoid.Coprod G H) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨b, hb⟩ := exists_ne (1 : H)
  let M := DifferentialGeometry.Algebra.Group.boolCoprodFamily G H
  let : Infinite (Monoid.CoprodI M) := infinite_coprodI_of_two_factors M
    (i := false) (j := true) Bool.false_ne_true
    (ULift.up a) (fun h => ha (congrArg ULift.down h))
    (ULift.up b) (fun h => hb (congrArg ULift.down h))
  exact Infinite.of_injective
    (DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod G H)
    (DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod G H).injective

theorem subsingleton_factor_of_finite_coprod (G : Type u) (H : Type v)
    [Group G] [Group H] [Finite (Monoid.Coprod G H)] : Subsingleton G ∨ Subsingleton H := by
  classical
  by_contra h
  have hG : ¬ Subsingleton G := fun hs => h (Or.inl hs)
  have hH : ¬ Subsingleton H := fun hs => h (Or.inr hs)
  let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hG
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
  let := infinite_coprod G H
  exact not_finite (Monoid.Coprod G H)

theorem finite_freeFactor_trivial_or_equiv {G H : Type u} [Group G] [Group H]
    [Finite H] (h : IsFreeFactor G H) : Subsingleton G ∨ Nonempty (G ≃* H) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  let : Finite (Monoid.Coprod G K) := Finite.of_equiv H e.toEquiv
  rcases subsingleton_factor_of_finite_coprod G K with hg | hk
  · exact Or.inl hg
  · let := hk
    let : Unique K := ⟨⟨1⟩, fun x => Subsingleton.elim x 1⟩
    let q : K ≃* PUnit.{u+1} := MulEquiv.ofUnique
    exact Or.inr ⟨((MulEquiv.coprodPUnit G).symm.trans
      ((MulEquiv.refl G).coprodCongr q.symm)).trans e.symm⟩

def FreelyIndecomposable (G : Type u) [Group G] : Prop :=
  ∀ (A B : Type u) [Group A] [Group B], Nonempty (G ≃* Monoid.Coprod A B) →
    Subsingleton A ∨ Subsingleton B

theorem finite_freelyIndecomposable (G : Type u) [Group G] [Finite G] :
    FreelyIndecomposable G := by
  intro A B hA hB he
  obtain ⟨e⟩ := he
  let : Finite (Monoid.Coprod A B) := Finite.of_equiv G e.toEquiv
  exact subsingleton_factor_of_finite_coprod A B

theorem finite_not_equiv_integer (G : Type u) [Group G] [Finite G] :
    ¬ Nonempty (G ≃* Multiplicative ℤ) := by
  rintro ⟨e⟩
  let : Finite (Multiplicative ℤ) := Finite.of_equiv G e.toEquiv
  let : Infinite (Multiplicative ℤ) := inferInstanceAs (Infinite ℤ)
  exact not_finite (Multiplicative ℤ)

theorem fg_factors_of_equiv_coprod {G : Type u} {A : Type v} {B : Type w}
    [Group G] [Group A] [Group B] [Group.FG G]
    (e : G ≃* Monoid.Coprod A B) : Group.FG A ∧ Group.FG B := by
  constructor
  · apply Group.fg_of_surjective (f := (Monoid.Coprod.lift (MonoidHom.id A) 1).comp e.toMonoidHom)
    intro a
    exact ⟨e.symm (Monoid.Coprod.inl a), by simp⟩
  · apply Group.fg_of_surjective (f := (Monoid.Coprod.lift 1 (MonoidHom.id B)).comp e.toMonoidHom)
    intro b
    exact ⟨e.symm (Monoid.Coprod.inr b), by simp⟩

theorem finite_freeFactor_card_dichotomy {G H : Type u} [Group G] [Group H]
    [Finite H] (h : IsFreeFactor G H) : Nat.card G = 1 ∨ Nat.card G = Nat.card H := by
  rcases finite_freeFactor_trivial_or_equiv h with hg | he
  · let := hg
    exact Or.inl (Nat.card_unique)
  · obtain ⟨e⟩ := he
    exact Or.inr (Nat.card_congr e.toEquiv)

theorem finite_freeFactor_card_le {G H : Type u} [Group G] [Group H]
    [Finite H] (h : IsFreeFactor G H) : Nat.card G ≤ Nat.card H := by
  rcases finite_freeFactor_card_dichotomy h with hg | hg
  · rw [hg]
    exact Nat.card_pos
  · exact hg.le

theorem finite_grushko_conditions (G : Type u) [Group G] [Finite G] [Nontrivial G] :
    Nontrivial G ∧ Group.FG G ∧ FreelyIndecomposable G ∧
      ¬ Nonempty (G ≃* Multiplicative ℤ) :=
  ⟨inferInstance, inferInstance, finite_freelyIndecomposable G, finite_not_equiv_integer G⟩

theorem freeFactor_fg_complement {G H : Type u} [Group G] [Group H] [Group.FG H]
    (h : IsFreeFactor G H) :
    Group.FG G ∧ ∃ (K : Type u) (_ : Group K),
      Group.FG K ∧ Nonempty (H ≃* Monoid.Coprod G K) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  obtain ⟨hg, hk⟩ := fg_factors_of_equiv_coprod e
  exact ⟨hg, K, hK, hk, ⟨e⟩⟩

end GC.Group
