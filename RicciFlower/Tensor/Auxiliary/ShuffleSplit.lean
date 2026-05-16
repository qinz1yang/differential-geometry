/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# Shuffle decomposition: splitting ModSumCongr at a distinguished element

Given types `α` and `β`, the quotient `Equiv.Perm.ModSumCongr α β` consists of
cosets of `Perm(α ⊕ β)` modulo block-permutations `sumCongr τ_l τ_r`.

When `α = Option α₀` (i.e., `α` has a distinguished element `none`), each permutation
`σ : Perm(α ⊕ β)` maps `Sum.inl none` to either the left block or the right block.
The **preimage** `σ⁻¹(Sum.inl none)` determines which side: this is well-defined on
`ModSumCongr` cosets because block-permutations preserve `Sum.inl` / `Sum.inr`.

## Main definitions

* `optionSumEquiv : Option α₀ ⊕ β ≃ Option (α₀ ⊕ β)` — the canonical equivalence
  sending `Sum.inl none ↦ none`.

## Main results

* `preimage_inl_none_side_well_defined` — the side of `σ⁻¹(inl none)` is invariant
  under right-multiplication by block-permutations.
-/

namespace ShuffleSplit

variable {α₀ : Type*} {β : Type*}

/-- The equivalence `Option α₀ ⊕ β ≃ Option (α₀ ⊕ β)` sending `Sum.inl none ↦ none`,
`Sum.inl (some a) ↦ some (Sum.inl a)`, `Sum.inr b ↦ some (Sum.inr b)`. -/
def optionSumEquiv : Option α₀ ⊕ β ≃ Option (α₀ ⊕ β) where
  toFun := fun x => match x with
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  invFun := fun x => match x with
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  left_inv := by intro x; rcases x with ((_ | a) | b) <;> rfl
  right_inv := by intro x; rcases x with (_ | (a | b)) <;> rfl

@[simp] theorem optionSumEquiv_inl_none :
    optionSumEquiv (Sum.inl (none : Option α₀) : Option α₀ ⊕ β) = none := rfl

@[simp] theorem optionSumEquiv_inl_some (a : α₀) :
    optionSumEquiv (Sum.inl (some a) : Option α₀ ⊕ β) = some (Sum.inl a) := rfl

@[simp] theorem optionSumEquiv_inr (b : β) :
    optionSumEquiv (Sum.inr b : Option α₀ ⊕ β) = some (Sum.inr b) := rfl

@[simp] theorem optionSumEquiv_symm_none :
    optionSumEquiv.symm (none : Option (α₀ ⊕ β)) = Sum.inl none := rfl

@[simp] theorem optionSumEquiv_symm_some_inl (a : α₀) :
    optionSumEquiv.symm (some (Sum.inl a) : Option (α₀ ⊕ β)) =
      Sum.inl (some a) := rfl

@[simp] theorem optionSumEquiv_symm_some_inr (b : β) :
    optionSumEquiv.symm (some (Sum.inr b) : Option (α₀ ⊕ β)) = Sum.inr b := rfl

/-! ### Well-definedness of side classification on ModSumCongr cosets -/

/-- Block-permutations preserve `Sum.inl`/`Sum.inr`, so the side of
`σ⁻¹(Sum.inl none)` is invariant under right-multiplication by block-permutations.
This means the side classification descends to `ModSumCongr` cosets. -/
theorem preimage_inl_none_side_well_defined
    (σ : Equiv.Perm (Option α₀ ⊕ β))
    (τ_l : Equiv.Perm (Option α₀)) (τ_r : Equiv.Perm β) :
    (∃ k, σ⁻¹ (Sum.inl none) = Sum.inl k) ↔
    (∃ k, (σ * Equiv.Perm.sumCongr τ_l τ_r)⁻¹ (Sum.inl none) = Sum.inl k) := by
  constructor <;> intro ⟨k, hk⟩
  · -- Forward: σ⁻¹(inl none) = inl k → (σ * sumCongr)⁻¹(inl none) = inl _
    refine ⟨τ_l⁻¹ k, ?_⟩
    simp only [mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.sumCongr_inv, Equiv.sumCongr_apply, hk, Sum.map_inl]
  · -- Backward: (σ * sumCongr)⁻¹(inl none) = inl k → σ⁻¹(inl none) = inl _
    rcases h : σ⁻¹ (Sum.inl (none : Option α₀)) with j | j
    · exact ⟨j, rfl⟩
    · exfalso
      have : (σ * Equiv.Perm.sumCongr τ_l τ_r)⁻¹ (Sum.inl none) =
          Sum.inr (τ_r⁻¹ j) := by
        simp only [mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply,
          Equiv.Perm.sumCongr_inv, Equiv.sumCongr_apply, h, Sum.map_inr]
      rw [hk] at this; exact absurd this (by simp)

/-- Variant using the `sumCongrHom` range subgroup. -/
theorem preimage_inl_none_side_well_defined'
    (σ : Equiv.Perm (Option α₀ ⊕ β))
    (τ : (Equiv.Perm.sumCongrHom (Option α₀) β).range) :
    (∃ k, σ⁻¹ (Sum.inl none) = Sum.inl k) ↔
    (∃ k, (σ * ↑τ)⁻¹ (Sum.inl none) = Sum.inl k) := by
  obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := τ.prop
  have : (↑τ : Equiv.Perm _) = Equiv.Perm.sumCongr τ_l τ_r := by
    rw [← hτ]; rfl
  rw [this]
  exact preimage_inl_none_side_well_defined σ τ_l τ_r

/-! ### `removeNone` as a group homomorphism on the stabilizer of `none`

For permutations of `Option α` that fix `none`, `Equiv.removeNone` is a group homomorphism:
it satisfies `removeNone(σ₁⁻¹ * σ₂) = (removeNone σ₁)⁻¹ * (removeNone σ₂)`.
This is proved via `optionCongr_injective`: both sides map to `σ₁⁻¹ * σ₂` under `optionCongr`. -/

/-- For a permutation `σ` of `Option α` fixing `none`, `optionCongr(removeNone σ) = σ`. -/
theorem optionCongr_removeNone_of_fix_none {α : Type*}
    (σ : Equiv.Perm (Option α)) (h : σ none = none) :
    (Equiv.removeNone σ).optionCongr = σ := by
  classical
  rw [map_equiv_removeNone, h]; simp

/-- `removeNone` is multiplicative on the stabilizer of `none`:
`removeNone(σ₁⁻¹ * σ₂) = (removeNone σ₁)⁻¹ * (removeNone σ₂)` when both fix `none`. -/
theorem removeNone_inv_mul {α : Type*}
    (σ₁ σ₂ : Equiv.Perm (Option α))
    (h₁ : σ₁ none = none) (h₂ : σ₂ none = none) :
    Equiv.removeNone (σ₁⁻¹ * σ₂) =
      (Equiv.removeNone σ₁)⁻¹ * Equiv.removeNone σ₂ := by
  classical
  apply Equiv.optionCongr_injective
  have h12 : (σ₁⁻¹ * σ₂) none = none := by simp [Equiv.Perm.coe_mul, h₁, h₂]
  have h12 : (σ₁⁻¹ * σ₂) none = none := by simp [Equiv.Perm.coe_mul, h₁, h₂]
  -- Strategy: show optionCongr of both sides are equal, then use optionCongr_injective.
  -- But optionCongr_injective : (α ≃ β) → ... , and both sides are α ≃ α.
  -- optionCongr(removeNone(σ₁⁻¹ * σ₂)) = σ₁⁻¹ * σ₂
  -- optionCongr((removeNone σ₁)⁻¹ * removeNone σ₂)
  --   = optionCongr((removeNone σ₁).symm.trans (removeNone σ₂))  -- by Perm.mul = Equiv.trans
  -- But Perm.mul ≠ Equiv.trans definitionally. Need a bridge.
  -- Just prove optionCongr of RHS = σ₁⁻¹ * σ₂ pointwise, then use injectivity.
  have h_lhs := optionCongr_removeNone_of_fix_none _ h12
  -- h_lhs : (removeNone(σ₁⁻¹ * σ₂)).optionCongr = σ₁⁻¹ * σ₂
  -- h_rhs: optionCongr of the RHS also equals σ₁⁻¹ * σ₂.
  -- Key helper: for σ fixing none, some(removeNone σ b) = σ(some b).
  have h_oc : ∀ (σ : Equiv.Perm (Option α)) (hσ : σ none = none) (b : α),
      some (Equiv.removeNone σ b) = σ (some b) := by
    intro σ hσ b
    have h := congr_fun (congr_arg DFunLike.coe
      (optionCongr_removeNone_of_fix_none σ hσ)) (some b)
    simp only [Equiv.optionCongr_apply] at h; exact h
  have h_rhs : ((Equiv.removeNone σ₁)⁻¹ * Equiv.removeNone σ₂).optionCongr =
      σ₁⁻¹ * σ₂ := by
    apply Equiv.Perm.ext; intro x; cases x with
    | none =>
      simp only [Equiv.optionCongr_apply, Equiv.Perm.coe_mul,
        Function.comp_apply, Equiv.Perm.inv_def]
      show Option.map _ none = _
      simp only [h₂]; exact (σ₁.symm_apply_eq.mpr h₁.symm).symm
    | some a =>
      simp only [Equiv.optionCongr_apply, Equiv.Perm.coe_mul,
        Function.comp_apply, Equiv.Perm.inv_def]
      change some ((Equiv.removeNone σ₁).symm ((Equiv.removeNone σ₂) a)) =
        σ₁.symm (σ₂ (some a))
      -- Goal: some ((rn σ₁).symm ((rn σ₂) a)) = σ₁.symm (σ₂ (some a))
      rw [← h_oc σ₂ h₂ a]
      -- Goal: some ((rn σ₁).symm ((rn σ₂) a)) = σ₁.symm (some ((rn σ₂) a))
      -- From h_oc σ₁: some(rn σ₁ b) = σ₁(some b), so σ₁.symm(some(rn σ₁ b)) = some b
      -- Applying σ₁.symm to both sides of h_oc: σ₁.symm(some(rn σ₁ b)) = some b
      -- So some((rn σ₁).symm c) = σ₁.symm(some c) for any c (take b = (rn σ₁).symm c).
      have : ∀ c, some ((Equiv.removeNone σ₁).symm c) = σ₁.symm (some c) := by
        intro c
        apply σ₁.injective
        rw [Equiv.apply_symm_apply, ← h_oc σ₁ h₁, Equiv.apply_symm_apply]
      exact this _
  -- Goal (after apply optionCongr_injective on line 124):
  -- (removeNone(σ₁⁻¹*σ₂)).optionCongr = ((removeNone σ₁)⁻¹ * removeNone σ₂).optionCongr
  exact h_lhs.trans h_rhs.symm

/-- For a permutation of `Option α` fixing `none`, `removeNone` preserves the sign. -/
theorem removeNone_sign {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm (Option α)) (h : σ none = none) :
    Equiv.Perm.sign (Equiv.removeNone σ) = Equiv.Perm.sign σ := by
  -- σ fixes none, so σ = (removeNone σ).optionCongr.
  -- sign((removeNone σ).optionCongr) = sign(removeNone σ) by optionCongr_sign.
  conv_rhs => rw [← optionCongr_removeNone_of_fix_none σ h]
  exact (Equiv.optionCongr_sign _).symm

/-- `Equiv.permCongr` preserves sign of permutations (since it's a conjugation). -/
theorem permCongr_sign {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    Equiv.Perm.sign (Equiv.permCongr e σ) = Equiv.Perm.sign σ := by
  exact Equiv.Perm.sign_permCongr _ _

/-- `Equiv.permCongr` commutes with `Equiv.Perm` inverse-multiply. -/
theorem permCongr_inv_mul {α β : Type*}
    (e : α ≃ β) (σ₁ σ₂ : Equiv.Perm α) :
    Equiv.permCongr e (σ₁⁻¹ * σ₂) =
      (Equiv.permCongr e σ₁)⁻¹ * Equiv.permCongr e σ₂ := by
  have h_inv : (Equiv.permCongr e σ₁ : Equiv.Perm _)⁻¹ =
      Equiv.permCongr e σ₁⁻¹ := by
    ext y
    change (Equiv.permCongr e σ₁).symm y = e (σ₁⁻¹ (e.symm y))
    simp [Equiv.permCongr_def, Equiv.Perm.inv_def]
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.permCongr_apply,
    h_inv, Equiv.symm_apply_apply]

end ShuffleSplit
