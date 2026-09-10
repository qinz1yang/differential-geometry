/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Logic.Equiv.Fin.Basic
import DifferentialGeometry.Topology.Algebra.Group.FiniteFreeProductInduction

set_option autoImplicit false

universe u

namespace Poincare.Algebra.Group


abbrev poincareStandardGroupFactors {a : ℕ} (Γ : Fin a → Type u) (b : ℕ) :
    Sum (Fin a) (Fin b) → Type u
  | Sum.inl j => Γ j
  | Sum.inr _ => ULift.{u} (Multiplicative ℤ)

instance poincareStandardGroupFactorsGroup {a : ℕ} (Γ : Fin a → Type u)
    [∀ j, Group (Γ j)] (b : ℕ) (i : Sum (Fin a) (Fin b)) :
    Group (poincareStandardGroupFactors Γ b i) := by
  cases i <;> simp only [poincareStandardGroupFactors] <;> infer_instance


abbrev poincareStandardFreeProduct {a : ℕ} (Γ : Fin a → Type u)
    [∀ j, Group (Γ j)] (b : ℕ) :=
  Monoid.CoprodI (poincareStandardGroupFactors Γ b)

theorem poincareStandardFreeProduct_subsingleton_iff
    {a : ℕ} (Γ : Fin a → Type u) [∀ j, Group (Γ j)] (b : ℕ) :
    Subsingleton (poincareStandardFreeProduct Γ b) ↔
      b = 0 ∧ ∀ j, Subsingleton (Γ j) := by
  rw [coprodI_subsingleton_iff]
  constructor
  · intro h
    constructor
    · apply Nat.eq_zero_of_not_pos
      intro hb
      let k : Fin b := ⟨0, hb⟩
      have hZ : Subsingleton (ULift.{u} (Multiplicative ℤ)) := h (Sum.inr k)
      have hone : ULift.up (Multiplicative.ofAdd (0 : ℤ)) =
          ULift.up (Multiplicative.ofAdd (1 : ℤ)) := hZ.elim _ _
      exact Int.zero_ne_one (congrArg (fun z => Multiplicative.toAdd z.down) hone)
    · intro j
      exact h (Sum.inl j)
  · rintro ⟨rfl, hΓ⟩ i
    cases i with
    | inl j => exact hΓ j
    | inr k => exact Fin.elim0 k

theorem poincareStandard_factors_trivial_of_equiv
    {a b : ℕ} (Γ : Fin a → Type u) [∀ j, Group (Γ j)]
    {K : Type u} [Group K] [Subsingleton K]
    (e : K ≃* poincareStandardFreeProduct Γ b) :
    b = 0 ∧ ∀ j, Subsingleton (Γ j) := by
  apply (poincareStandardFreeProduct_subsingleton_iff Γ b).1
  exact e.symm.subsingleton

noncomputable def finiteFreeProductPoincareStandardEquiv
    {a : ℕ} (Gamma : Fin a → Type u) [∀ j, Group (Gamma j)] (b : ℕ)
    (G P : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (P n)]
    (base : P 0 ≃* PUnit)
    (step : ∀ n, P (Nat.succ n) ≃* Monoid.Coprod (P n) (G n))
    (factorEquiv : ∀ i : Fin (a + b),
      finFreeProductFamily G (a + b) i ≃*
        poincareStandardGroupFactors Gamma b (finSumFinEquiv.symm i)) :
    P (a + b) ≃* poincareStandardFreeProduct Gamma b :=
  (finiteFreeProductEquiv G P base step (a + b)).trans
    (coprodIReindexEquiv
      (finFreeProductFamily G (a + b))
      (poincareStandardGroupFactors Gamma b)
      finSumFinEquiv.symm factorEquiv)

theorem finiteFreeProductPoincareStandardEquiv_comp_factorToStage
    {a : ℕ} (Gamma : Fin a → Type u) [∀ j, Group (Gamma j)] (b : ℕ)
    (G P : ℕ → Type u) [∀ n, Group (G n)] [∀ n, Group (P n)]
    (base : P 0 ≃* PUnit)
    (step : ∀ n, P (Nat.succ n) ≃* Monoid.Coprod (P n) (G n))
    (factorEquiv : ∀ i : Fin (a + b),
      finFreeProductFamily G (a + b) i ≃*
        poincareStandardGroupFactors Gamma b (finSumFinEquiv.symm i))
    (i : Fin (a + b)) :
    (finiteFreeProductPoincareStandardEquiv Gamma b G P base step factorEquiv).toMonoidHom.comp
        (finiteFactorToStage G P step (a + b) i) =
      (Monoid.CoprodI.of :
        poincareStandardGroupFactors Gamma b (finSumFinEquiv.symm i) →*
          poincareStandardFreeProduct Gamma b).comp
        (factorEquiv i).toMonoidHom := by
  change
    (coprodIReindexEquiv
      (finFreeProductFamily G (a + b))
      (poincareStandardGroupFactors Gamma b)
      finSumFinEquiv.symm factorEquiv).toMonoidHom.comp
        ((finiteFreeProductEquiv G P base step (a + b)).toMonoidHom.comp
          (finiteFactorToStage G P step (a + b) i)) = _
  rw [finiteFreeProductEquiv_comp_factorToStage]
  exact coprodIReindexEquiv_comp_of
    (finFreeProductFamily G (a + b))
    (poincareStandardGroupFactors Gamma b)
    finSumFinEquiv.symm factorEquiv i

end Poincare.Algebra.Group
