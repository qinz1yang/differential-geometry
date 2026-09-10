/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.GroupTheory.PushoutI

set_option autoImplicit false

universe u v w

namespace Poincare.Algebra.Group

theorem pushoutI_existsUnique_lift {ι : Type u} [Nonempty ι]
    (G : ι → Type v) (H : Type w) [∀ i, Group (G i)] [Group H]
    (φ : ∀ i, H →* G i) {K : Type*} [Group K]
    (f : ∀ i, G i →* K) (k : H →* K) (hf : ∀ i, (f i).comp (φ i) = k) :
    ∃! F : Monoid.PushoutI φ →* K,
      ∀ i, F.comp (Monoid.PushoutI.of i) = f i := by
  refine ⟨Monoid.PushoutI.lift f k hf, ?_, ?_⟩
  · intro i
    ext g
    simp
  · intro F hF
    apply Monoid.PushoutI.hom_ext_nonempty
    intro i
    rw [hF i]
    ext g
    simp

theorem pushoutI_subsingleton_of_factors {ι : Type u} [Nonempty ι]
    (G : ι → Type v) (H : Type w) [∀ i, Group (G i)] [Group H]
    (φ : ∀ i, H →* G i) [∀ i, Subsingleton (G i)] :
    Subsingleton (Monoid.PushoutI φ) := by
  constructor
  intro x y
  suffices htrivial : ∀ z : Monoid.PushoutI φ, z = 1 by
    exact (htrivial x).trans (htrivial y).symm
  intro z
  induction z using Monoid.PushoutI.induction_on with
  | of i g =>
      rw [Subsingleton.elim g 1, map_one]
  | base h =>
      let i : ι := Classical.choice inferInstance
      rw [← Monoid.PushoutI.of_apply_eq_base φ i h]
      rw [Subsingleton.elim (φ i h) 1, map_one]
  | mul a b ha hb =>
      rw [ha, hb, mul_one]

namespace PushoutIdentities

abbrev factor : Bool → Type
  | false => PUnit
  | true => Multiplicative ℤ

instance factorGroup (i : Bool) : Group (factor i) := by
  cases i <;> simp only [factor] <;> infer_instance

def diagram : ∀ i : Bool, Multiplicative ℤ →* factor i
  | false => 1
  | true => MonoidHom.id _

theorem of_true_eq_one (h : Multiplicative ℤ) :
    Monoid.PushoutI.of true h = (1 : Monoid.PushoutI diagram) := by
  calc
    Monoid.PushoutI.of true h = Monoid.PushoutI.base diagram h := by
      simpa [diagram] using Monoid.PushoutI.of_apply_eq_base diagram true h
    _ = Monoid.PushoutI.of false (1 : PUnit) := by
      simpa [diagram] using (Monoid.PushoutI.of_apply_eq_base diagram false h).symm
    _ = 1 := map_one _

theorem of_true_not_injective :
    ¬ Function.Injective
      (Monoid.PushoutI.of (φ := diagram) true :
        Multiplicative ℤ →* Monoid.PushoutI diagram) := by
  intro hinj
  have hEq : Multiplicative.ofAdd (1 : ℤ) = 1 := hinj <| by
    rw [of_true_eq_one]
    exact (map_one _).symm
  have hEq' := congrArg Multiplicative.toAdd hEq
  change (1 : ℤ) = 0 at hEq'
  exact one_ne_zero hEq'

end PushoutIdentities

end Poincare.Algebra.Group
