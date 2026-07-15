/-
Authors: Yuan Liao, Jack McCarthy
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
/-!
# Tensor-Hom Equivalence and Induced Norm

This file establishes the tensor-hom equivalence for finite-dimensional normed spaces
and uses it to induce a normed space structure on the tensor product `F₁ ⊗[𝕜] F₂`.

## Main Definitions

* `tensorHomEquiv` : linear equivalence `F₁ ⊗ F₂ ≃ₗ (Dual F₁ →ₗ F₂)`.
* `cDual` : the normed (continuous) dual `F₁ →L[𝕜] 𝕜`.
* `clmEquiv` : linear equivalence `F₁ ⊗ F₂ ≃ₗ (cDual F₁ →L F₂)`.
* `instNormedAddCommGroup_tensor` : induced normed group structure on `F₁ ⊗ F₂`.
* `instNormedSpace_tensor` : induced normed space structure on `F₁ ⊗ F₂`.

## Tags

tensor product, hom equivalence, normed space, dual
-/

open scoped Topology TensorProduct

noncomputable section

/-! ## Induced norm on tensor product -/

section TensorNorm

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

omit [FiniteDimensional 𝕜 F₂] in
/-- In finite dimensions, finrank of continuous linear maps equals the product of finranks. -/
lemma finrank_continuousLinearMap' :
    Module.finrank 𝕜 (F₁ →L[𝕜] F₂) = Module.finrank 𝕜 F₁ * Module.finrank 𝕜 F₂ := by
  have e : (F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  rw [e.finrank_eq, Module.finrank_linearMap 𝕜 𝕜]

/-- Linear equivalence between tensor product and Hom from dual, by dimension counting. -/
noncomputable def tensorHomEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] ((Module.Dual 𝕜 F₁) →ₗ[𝕜] F₂) := by
  let f : Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ≃ₗ[𝕜] F₁ := (Module.evalEquiv 𝕜 F₁).symm
  have h₀ : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) ⊗[𝕜] F₂ ≃ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
    let g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
      TensorProduct.lift ((TensorProduct.mk 𝕜 F₁ F₂) ∘ₗ f.toLinearMap)
    let ginv : (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) :=
      TensorProduct.lift
        ((TensorProduct.mk 𝕜 (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) F₂) ∘ₗ f.symm.toLinearMap)
    have left_inv₀ : ginv ∘ₗ g = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have left_inv : ∀ x, ginv (g x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ ginv g x]
      have h : (ginv ∘ₗ g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →
        (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂)) = ginv ∘ g := by simp
      rw [←h, left_inv₀]
      simp
    have right_inv₀ : g ∘ₗ ginv = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have right_inv : ∀ x, g (ginv x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ g ginv x]
      have h : (g ∘ₗ ginv : (F₁ ⊗[𝕜] F₂) → (F₁ ⊗[𝕜] F₂)) = g ∘ ginv := by simp
      rw [←h, right_inv₀]
      simp
    LinearEquiv.mk g ginv left_inv right_inv
  have h₁ := (dualTensorHomEquiv 𝕜 (Module.Dual 𝕜 F₁) F₂)
  exact LinearEquiv.trans (LinearEquiv.symm h₀) h₁
-- note jack's ones

/-- The normed (continuous) dual of `F₁`. -/
abbrev cDual := F₁ →L[𝕜] 𝕜

/--
Auxiliary bilinear map for the tensor–hom adjunction:
`v : F₁`, `w : F₂` ↦ (φ ↦ φ v • w) as a *continuous* linear map `cDual →L F₂`.

We build it as a linear map and use `LinearMap.toContinuousLinearMap` relying on
finite-dimensionality of the domain.
-/
noncomputable def toHomAux :
    F₁ →ₗ[𝕜] F₂ →ₗ[𝕜] (cDual (𝕜:=𝕜) (F₁:=F₁) →L[𝕜] F₂) :=
by
  classical

  refine
    { toFun := fun v =>
        { toFun := fun w =>
            ({
              toFun := fun φ => (φ v) • w
              map_add' := by
                intro φ ψ
                simp [add_smul]
              map_smul' := by
                intro a φ

                simp [mul_smul]
            } : (cDual (𝕜:=𝕜) (F₁:=F₁) →ₗ[𝕜] F₂)).toContinuousLinearMap
          map_add' := by
            intro w₁ w₂
            ext φ
            simp [smul_add]
          map_smul' := by
            intro a w
            ext φ
            simp [smul_smul, mul_comm] }
      map_add' := by
        intro v₁ v₂
        ext w φ
        simp [add_smul]
      map_smul' := by
        intro a v
        ext w φ

        simp [mul_smul] }

/--
The induced linear map `F₁ ⊗[𝕜] F₂ →ₗ[𝕜] (cDual →L[𝕜] F₂)` by the universal property.
-/
noncomputable def toHom :
    (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual (𝕜:=𝕜) (F₁:=F₁) →L[𝕜] F₂) :=
_root_.TensorProduct.lift (toHomAux (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂))


omit [FiniteDimensional 𝕜 F₂]
/-- In finite dimensions, finrank of continuous linear maps equals the product of finranks. -/
lemma finrank_continuousLinearMap :
    Module.finrank 𝕜 (F₁ →L[𝕜] F₂) = Module.finrank 𝕜 F₁ * Module.finrank 𝕜 F₂ := by

  haveI : Module.Free 𝕜 F₁ := inferInstance
  haveI : Module.Free 𝕜 F₂ := inferInstance
  have e : (F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  rw [e.finrank_eq]
  rw [Module.finrank_linearMap 𝕜 𝕜]

/-- The continuous dual `cDual 𝕜 F₁` is linearly equivalent to the algebraic dual
`Module.Dual 𝕜 F₁`, since all linear maps are continuous in finite dimensions. -/
def cDual_eqiv_dual : cDual 𝕜 F₁ ≃ₗ[𝕜] Module.Dual 𝕜 F₁ := by
  unfold cDual Module.Dual
  exact (@LinearMap.toContinuousLinearMap 𝕜 _ F₁ _ _ _ _ _ 𝕜 _ _ _ _ _ _ _ _).symm

/-- Continuous linear maps out of the continuous dual are equivalent to linear maps out of
the algebraic dual, since `cDual ≃ₗ Module.Dual` in finite dimensions. -/
def cDual_clm_equiv_dual_lm : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) := by
  have e : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  have e' : (cDual 𝕜 F₁ →ₗ[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) :=
    LinearEquiv.congrLeft F₂ 𝕜 (cDual_eqiv_dual 𝕜 F₁)
  exact LinearEquiv.trans e e'

/--
A *linear equivalence* `F₁ ⊗ F₂ ≃ₗ (cDual →L F₂)` obtained by dimension counting.

This matches your "equivalence by finrank" pattern.  (It's coordinate-free: no
`Fin n → 𝕜` coordinates.)
-/
noncomputable def clmEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂) :=
  LinearEquiv.trans (tensorHomEquiv 𝕜 F₁ F₂) (cDual_clm_equiv_dual_lm 𝕜 F₁ F₂).symm

/-- Induced normed additive commutative group structure on `F₁ ⊗[𝕜] F₂`, pulled back
along the equivalence `clmEquiv : F₁ ⊗ F₂ ≃ₗ (cDual F₁ →L F₂)`. -/
noncomputable instance instNormedAddCommGroup_tensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)

  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_

  exact e.injective

/-- Induced normed `𝕜`-module structure on `F₁ ⊗[𝕜] F₂`, pulled back along `clmEquiv`. -/
noncomputable instance instNormedSpace_tensor :
    NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)

  refine NormedSpace.induced
    (F := (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂))
    (𝕜 := 𝕜)
    (E := (F₁ ⊗[𝕜] F₂))
    (G := (cDual 𝕜 F₁ →L[𝕜] F₂))
    e.toLinearMap

end TensorNorm
