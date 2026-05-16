import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
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
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.VectorField

open scoped Topology
open scoped TensorProduct

/-
# The vector bundle of tensor products

We define the (topological) vector bundle of tensor products of two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*` and normed spaces `F₁` and `F₂`, we define a vector bundle
with fiber `E₁ x ⊗[𝕜] E₂ x` and model fiber `F₁ ⊗[𝕜] F₂`.
-/

noncomputable section

open Bundle Set Topology
open scoped Bundle TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

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
  -- First: for each `v w`, define a linear map `cDual →ₗ F₂`, then make it continuous.
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
                -- (a•φ) v = a*(φ v)
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
        -- φ (a•v) = a*(φ v)
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
  -- In finite dimensions, E →L[𝕜] F ≃ₗ E →ₗ[𝕜] F
  haveI : Module.Free 𝕜 F₁ := inferInstance
  haveI : Module.Free 𝕜 F₂ := inferInstance
  have e : (F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  rw [e.finrank_eq]
  rw [Module.finrank_linearMap 𝕜 𝕜]



def cDual_eqiv_dual : cDual 𝕜 F₁ ≃ₗ[𝕜] Module.Dual 𝕜 F₁ := by
  unfold cDual Module.Dual
  exact (@LinearMap.toContinuousLinearMap 𝕜 _ F₁ _ _ _ _ _ 𝕜 _ _ _ _ _ _ _ _).symm

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


noncomputable instance instNormedAddCommGroup_tensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  -- pick 𝓕 := AddMonoidHom
  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_
  -- injectivity of the underlying function
  exact e.injective


/-- Induced normed space structure on tensor product. -/
noncomputable instance instNormedSpace_tensor :
    NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  -- Choose the “linear map-like” type explicitly:
  refine NormedSpace.induced
    (F := (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂))
    (𝕜 := 𝕜)
    (E := (F₁ ⊗[𝕜] F₂))
    (G := (cDual 𝕜 F₁ →L[𝕜] F₂))
    e.toLinearMap



end TensorNorm

/-- The tensor product map `(v, w) ↦ v ⊗ₜ w` as a continuous bilinear map. -/
noncomputable def TensorProduct.tmulL :
    F₁ →L[𝕜] F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) := by
  classical
  let innerLM (v : F₁) : F₂ →ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
    TensorProduct.mk 𝕜 F₁ F₂ v
  let innerCLM (v : F₁) : F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
    (innerLM v).toContinuousLinearMap
  let outerLM : F₁ →ₗ[𝕜] F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
    { toFun := fun v => innerCLM v
      map_add' := by
        intro v v'
        ext w
        simp [innerCLM, innerLM]
      map_smul' := by
        intro c v
        ext w
        simp [innerCLM, innerLM] }
  exact outerLM.toContinuousLinearMap

@[simp]
theorem TensorProduct.tmulL_apply (v : F₁) (w : F₂) :
    TensorProduct.tmulL (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂) v w = v ⊗ₜ[𝕜] w := by
  simp [TensorProduct.tmulL]

/-! ## TensorProduct.mapL and its properties -/

section MapL

variable {G₁ G₂ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]

/-- `TensorProduct.map` as a continuous linear map in finite dimensions. -/
noncomputable def TensorProduct.mapL (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    (F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂) :=
  (TensorProduct.map L₁.toLinearMap L₂.toLinearMap).toContinuousLinearMap

omit [FiniteDimensional 𝕜 G₂] in
@[simp]
theorem TensorProduct.mapL_tmul (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) (v : F₁) (w : F₂) :
    TensorProduct.mapL L₁ L₂ (v ⊗ₜ w) = L₁ v ⊗ₜ L₂ w := by
  simp [TensorProduct.mapL, TensorProduct.map_tmul]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapL_add_left (L₁ L₁' : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL (L₁ + L₁') L₂ = TensorProduct.mapL L₁ L₂ + TensorProduct.mapL L₁' L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_add_left]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapL_add_right (L₁ : F₁ →L[𝕜] G₁) (L₂ L₂' : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL L₁ (L₂ + L₂') = TensorProduct.mapL L₁ L₂ + TensorProduct.mapL L₁ L₂' := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_add_right]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapL_smul_left (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL (c • L₁) L₂ = c • TensorProduct.mapL L₁ L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_smul_left]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapL_smul_right (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapL L₁ (c • L₂) = c • TensorProduct.mapL L₁ L₂ := by
  ext x; simp [TensorProduct.mapL, TensorProduct.map_smul_right]


/-- The bilinear map (L₁, L₂) ↦ TensorProduct.mapL L₁ L₂. -/
noncomputable def TensorProduct.mapLBilinear :
    (F₁ →L[𝕜] G₁) →L[𝕜] (F₂ →L[𝕜] G₂) →L[𝕜]
      ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) := by
  classical
  -- continuity will be obtained from finite-dimensionality of the domains
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] G₁) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F₂ →L[𝕜] G₂) := ContinuousLinearMap.finiteDimensional
  -- inner: linear in L₂
  let innerLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →ₗ[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    { toFun := fun L₂ => TensorProduct.mapL (𝕜 := 𝕜) L₁ L₂
      map_add' := TensorProduct.mapL_add_right (𝕜 := 𝕜) (L₁ := L₁)
      map_smul' := fun c L₂ =>
        TensorProduct.mapL_smul_right (𝕜 := 𝕜) (L₁ := L₁) (L₂ := L₂) c }
  let innerCLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    (innerLM (L₁ := L₁)).toContinuousLinearMap
  -- outer: linear in L₁, valued in continuous linear maps (in L₂)
  let outerLM :
      (F₁ →L[𝕜] G₁) →ₗ[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    { toFun := fun L₁ => innerCLM (L₁ := L₁)
      map_add' := by
        intro L₁ L₁'
        ext L₂ x
        -- evaluate in the codomain to reduce to your previously proved lemma
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapL_add_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) (L₁' := L₁'))
      map_smul' := by
        intro c L₁
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapL_smul_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) c) }
  letI : NormedAddCommGroup
      ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) := inferInstance
  letI : NormedSpace 𝕜
      ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) := inferInstance
  exact outerLM.toContinuousLinearMap


end MapL


namespace Pretrivialization

/-! ## Pretrivialization for tensor product bundle -/

/-- The coordinate change function for tensor product bundles.

Compare with `continuousLinearMapCoordChange` for Hom bundles:
- Hom: `L ↦ (coordChange e₂ e₂') ∘ L ∘ (coordChange e₁' e₁)` (note reversed order on first factor)
- Tensor: `v ⊗ w ↦ (coordChange e₁ e₁' v) ⊗ (coordChange e₂ e₂' w)` (same direction)
-/
def tensorProductCoordChange [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]
    (b : B) : (F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
  TensorProduct.mapL (e₁.coordChangeL 𝕜 e₁' b) (e₂.coordChangeL 𝕜 e₂' b)

variable {e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

theorem continuousOn_tensorProductCoordChange
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContinuousOn (tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  classical
  have h₁ := continuousOn_coordChange 𝕜 e₁ e₁'
  have h₂ := continuousOn_coordChange 𝕜 e₂ e₂'
  let s : Set B := (e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have hs1 : s ⊆ (e₁.baseSet ∩ e₁'.baseSet) := fun b hb => ⟨hb.1.1, hb.2.1⟩
  have hs2 : s ⊆ (e₂.baseSet ∩ e₂'.baseSet) := fun b hb => ⟨hb.1.2, hb.2.2⟩
  have h₁' : ContinuousOn (fun b => (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)) s :=
    h₁.mono hs1
  have h₂' : ContinuousOn (fun b => (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    h₂.mono hs2
  -- The uncurried bilinear map (L₁, L₂) ↦ mapLBilinear L₁ L₂ is continuous
  have huncurry : Continuous (fun p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂) =>
                              TensorProduct.mapLBilinear p.1 p.2) :=
    (TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂)
      (G₁ := F₁) (G₂ := F₂)).continuous₂
  have hprod : ContinuousOn (fun b =>
        ((e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁),
         (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂))) s :=
    h₁'.prodMk h₂'
  refine (huncurry.comp_continuousOn hprod).congr ?_
  intro b hb
  simp [tensorProductCoordChange, TensorProduct.mapLBilinear, TensorProduct.mapL]

variable (𝕜 e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]




/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.tensorProduct e₁ e₂` is the induced pretrivialization for the
tensor product `E₁ ⊗ E₂`. -/
def tensorProduct :
    Pretrivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) where
  toFun p := ⟨p.1, TensorProduct.map
    (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
    (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩
  invFun p := ⟨p.1, TensorProduct.map
    (e₁.symmL 𝕜 p.1).toLinearMap
    (e₂.symmL 𝕜 p.1).toLinearMap p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, v⟩ ⟨h₁, h₂⟩ ↦ by
      simp only [TotalSpace.mk_inj]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.symmL 𝕜 x).toLinearMap.comp (e₁.continuousLinearMapAt 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        -- 'apply' handles the def-eq between x and (⟨x,v⟩).proj automatically
        apply Trivialization.symmL_continuousLinearMapAt e₁ h₁
      have eq2 : (e₂.symmL 𝕜 x).toLinearMap.comp (e₂.continuousLinearMapAt 𝕜 x).toLinearMap =
        LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.symmL_continuousLinearMapAt e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]

  right_inv' := fun ⟨x, t⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
      simp only [Prod.mk.injEq, true_and]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₁.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₁ h₁
      have eq2 : (e₂.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₂.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_apply (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    (tensorProduct 𝕜 e₁ e₂) p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl


instance tensorProduct.isLinear
    [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.tensorProduct 𝕜 e₁ e₂).IsLinear 𝕜 where
  linear x hx :=
  by
    classical
    refine
      { map_add := ?_
        map_smul := ?_ }
    · intro t t'
      -- after unfolding, goal is about `TensorProduct.map ... (t + t')`
      -- and `simp` can use the generic `map_add`
      simp [Pretrivialization.tensorProduct_apply]
    · intro c t
      simp [Pretrivialization.tensorProduct_apply]

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_symm_apply (p : B × (F₁ ⊗[𝕜] F₂)) :
    (tensorProduct 𝕜 e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, TensorProduct.map
        (e₁.symmL 𝕜 p.1).toLinearMap
        (e₂.symmL 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (t : F₁ ⊗[𝕜] F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b t =
      TensorProduct.map
        (e₁.symmL 𝕜 b).toLinearMap
        (e₂.symmL 𝕜 b).toLinearMap t := by
  -- This is the key: use `symm_apply` instead of unfolding `Pretrivialization.symm`.
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

theorem tensorProductCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (t : F₁ ⊗[𝕜] F₂) :
    tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b t =
      (tensorProduct 𝕜 e₁' e₂' ⟨b, (tensorProduct 𝕜 e₁ e₂).symm b t⟩).2 := by
  -- Step A: rewrite RHS using the helper lemma, so no `dif` / `cast` appears.
  -- First unfold coord change and `mapL` once.
  simp only [tensorProductCoordChange, TensorProduct.mapL]
  -- Now expand the RHS pretrivialization using your `tensorProduct_apply`
  -- and rewrite `.symm b t` using `tensorProduct_symm_apply'`.
  -- This should turn RHS into a `TensorProduct.map ... (TensorProduct.map ... t)`.
  simp only [LinearMap.coe_toContinuousLinearMap',
    tensorProduct_symm_apply' (𝕜 := 𝕜) (e₁ := e₁) (e₂ := e₂) hb.1,
    tensorProduct_apply]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  -- Step C: identify the composed linear maps with coordChange maps.
  -- You’ll now have two component goals, one for F₁ and one for F₂.
  congr 1 ; ext v
  rename_i v x
  have hb1 : b ∈ e₁.baseSet ∩ e₁'.baseSet := ⟨hb.1.1, hb.2.1⟩
  have hb2 : b ∈ e₂.baseSet ∩ e₂'.baseSet := ⟨hb.1.2, hb.2.2⟩
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, LinearMap.coe_comp, Trivialization.continuousLinearMapAt_apply,
    Trivialization.symmL_apply, Function.comp_apply]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₁) (e' := e₁') (b := b) hb1 (y := v)]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₂) (e' := e₂') (b := b) hb2 (y := x)]
  simp [TensorProduct.tmul, Trivialization.linearMapAt]
  simp [Pretrivialization.linearMapAt]
  have hb1' : b ∈ e₁'.toPretrivialization.baseSet := by simpa using hb.2.1
  have hb2' : b ∈ e₂'.toPretrivialization.baseSet := by simpa using hb.2.2
  simp [ hb1', hb2']
  rfl



end Pretrivialization
section
section TensorFiberTopology

open scoped TensorProduct
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

@[reducible]
noncomputable def tensorFiberTopologicalSpace (x : B) :
    TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := by
  classical
  -- ensure model tensor has a topology
  letI : TopologicalSpace (F₁ ⊗[𝕜] F₂) := inferInstance
  let L₁ : E₁ x ≃L[𝕜] F₁ :=
    (trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₁ E₁ x)
  let L₂ : E₂ x ≃L[𝕜] F₂ :=
    (trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₂ E₂ x)
  exact TopologicalSpace.induced
    (fun t : E₁ x ⊗[𝕜] E₂ x =>
      TensorProduct.map L₁.toLinearMap L₂.toLinearMap t)
    inferInstance



-- A fully explicit declaration avoids synthesis-order issues for an anonymous local instance.
@[reducible]
noncomputable def tensorFiberTopologicalSpaceInst
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type*) [TopologicalSpace B]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂) x

theorem tensorFiberTopologicalSpaceInst_eq
    (x : B) :
    tensorFiberTopologicalSpaceInst 𝕜 B F₁ F₂ E₁ E₂ x =
      tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
        (E₁ := E₁) (E₂ := E₂) x := rfl



end TensorFiberTopology

section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂
namespace Bundle.TensorProduct

open Bundle Set Topology Pretrivialization
open scoped Manifold Bundle TensorProduct


class TensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    Type (max uB (max (uE₁+1) (uE₂+1))) where
  (fiberTop : ∀ x : B, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x))

attribute [instance] TensorFiberTopologies.fiberTop

class TensorBundleCore
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    extends TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ where
  totalSpaceTop :
    TopologicalSpace (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))
  fiberBundleInst :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      totalSpaceTop
      toTensorFiberTopologies.fiberTop
  vectorBundleInst :
    letI := totalSpaceTop
    letI := fiberBundleInst
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)

attribute [instance] TensorBundleCore.totalSpaceTop
attribute [instance] TensorBundleCore.fiberBundleInst
attribute [instance] TensorBundleCore.vectorBundleInst
attribute [instance] TensorBundleCore.toTensorFiberTopologies

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
     [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₂ E₂] [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]




noncomputable instance instNormedAddCommGroup_tensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  -- pick 𝓕 := AddMonoidHom
  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_
  -- injectivity of the underlying function
  exact e.injective

noncomputable instance instNormedSpace_model_tensor :
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

@[reducible]
noncomputable def tensorFiberTopology (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := by
  classical
  letI : TopologicalSpace (F₁ ⊗[𝕜] F₂) := inferInstance
  let e₁ := trivializationAt F₁ E₁ x
  let e₂ := trivializationAt F₂ E₂ x
  let L₁ : E₁ x ≃L[𝕜] F₁ :=
    e₁.continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt F₁ E₁ x)
  let L₂ : E₂ x ≃L[𝕜] F₂ :=
    e₂.continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt F₂ E₂ x)
  exact TopologicalSpace.induced
    (fun t : E₁ x ⊗[𝕜] E₂ x => TensorProduct.map L₁.toLinearMap L₂.toLinearMap t)
    inferInstance

noncomputable instance tensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ :=
  ⟨fun x =>
    tensorFiberTopology (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x⟩
-- noncomputable def tensorFiberTopology (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
--   tensorFiberTopologicalSpace (F₁ := F₁) (F₂ := F₂) E₁ E₂ x


noncomputable def vectorPrebundle :
    @VectorPrebundle
      𝕜                                  -- R
      B                                  -- B
      (F₁ ⊗[𝕜] F₂)                       -- F
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)           -- E
      _                                  -- [NontriviallyNormedField 𝕜]
      _                                  -- [∀ x, AddCommMonoid (E x)]
      _                                  -- [∀ x, Module 𝕜 (E x)]
      instNormedAddCommGroup_tensor -- [NormedAddCommGroup F]
      instNormedSpace_model_tensor        -- [NormedSpace 𝕜 F]
      _                                  -- [TopologicalSpace B]
      (fun x => tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) x)
      -- [∀ x, TopologicalSpace (E x)]
      :=
  letI := tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂)
  {
    pretrivializationAtlas :=
      {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct (𝕜 := 𝕜) e₁ e₂}
    pretrivialization_linear' := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
      apply Pretrivialization.tensorProduct.isLinear


    pretrivializationAt := fun x =>
      Pretrivialization.tensorProduct (𝕜 := 𝕜) (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
    mem_base_pretrivializationAt := fun x =>
      ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
    pretrivialization_mem_atlas := fun x =>
      ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
    exists_coordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      refine ⟨Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) (e₁ := e₁) (e₁' := e₁')
                (e₂ := e₂) (e₂' := e₂'),
              ?_, Pretrivialization.tensorProductCoordChange_apply (𝕜 := 𝕜)
                (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')⟩
      simpa using
        (Pretrivialization.continuousOn_tensorProductCoordChange (𝕜 := 𝕜)
          (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂'))
    totalSpaceMk_isInducing := by
      intro b
      -- 1. Setup local definitions
      letI : TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
         tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) b
      let L₁ : E₁ b ≃L[𝕜] F₁ :=
        (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      let L₂ : E₂ b ≃L[𝕜] F₂ :=
        (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      -- 2. Prove induction
      have hind : IsInducing (TensorProduct.map L₁.toLinearMap L₂.toLinearMap) := ⟨rfl⟩
      have : IsInducing fun x ↦ (b, TensorProduct.map L₁.toLinearMap L₂.toLinearMap x) :=
        isInducing_const_prod.mpr hind
      convert this using 1
      funext x
      simp only [Function.comp_apply, Pretrivialization.tensorProduct_apply,
                  Prod.mk.injEq, true_and]
      have hL1 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₁ E₁ b) b) :
              E₁ b →ₗ[𝕜] F₁) =
            (↑L₁.toLinearEquiv : E₁ b →ₗ[𝕜] F₁) := by
        ext w
 -- `L₁` is defined as `continuousLinearEquivAt`, and its underlying map is `continuousLinearMapAt`
        simpa [L₁] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₁ E₁ b)
              (mem_baseSet_trivializationAt F₁ E₁ b)).symm
      have hL2 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₂ E₂ b) b) :
              E₂ b →ₗ[𝕜] F₂) =
            (↑L₂.toLinearEquiv : E₂ b →ₗ[𝕜] F₂) := by
        ext w
        simpa [L₂] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₂ E₂ b)
              (mem_baseSet_trivializationAt F₂ E₂ b)).symm
      -- now the two `TensorProduct.map`’s are definitionally the same
      simp [hL1, hL2]

  }


/-- Topology on the total space of the tensor product bundle. -/
@[reducible]
noncomputable def totalSpaceTopology :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  -- provide fiber topologies locally
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x
  -- now identical to the sample
  exact
    (Bundle.TensorProduct.vectorPrebundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology

@[reducible]
noncomputable def tensorFiberTop :
    (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
  fun b =>
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) b

@[reducible]
noncomputable def tensorTotalSpaceTop :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology

attribute [local instance] tensorTotalSpaceTop

/-- The tensor product of two vector bundles forms a fiber bundle. -/
@[reducible]
noncomputable def fiberBundle :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)
      (tensorTotalSpaceTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂))
      (tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)) := by
  classical
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toFiberBundle

attribute [local instance] fiberBundle

/-- The tensor product of two vector bundles forms a vector bundle. -/
@[reducible]
noncomputable def vectorBundle :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toVectorBundle

noncomputable instance tensorBundleCore :
    TensorBundleCore 𝕜 B F₁ F₂ E₁ E₂ where
  toTensorFiberTopologies :=
    tensorFiberTopologies
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  totalSpaceTop :=
    totalSpaceTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  fiberBundleInst :=
    fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  vectorBundleInst := by
    classical
    simp [vectorBundle
          (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)]


variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂`,
the induced trivialization for the tensor product bundle. -/
noncomputable def _root_.Bundle.Trivialization.tensorProduct :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    VectorPrebundle.trivializationOfMemPretrivializationAtlas _
      ⟨e₁, e₂, he₁, he₂, rfl⟩


noncomputable instance memTrivializationAtlas :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    MemTrivializationAtlas
      (e₁.tensorProduct (𝕜 := 𝕜) e₂ :
        Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  refine ⟨?_⟩
  exact ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩, rfl⟩

@[simp]
theorem _root_.Bundle.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct (𝕜 := 𝕜) e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem _root_.Bundle.Trivialization.tensorProduct_apply
    (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct (𝕜 := 𝕜) e₂ p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

theorem tensorProduct_trivializationAt (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ =
      (trivializationAt F₁ E₁ x₀).tensorProduct (𝕜 := 𝕜) (trivializationAt F₂ E₂ x₀) := rfl

theorem tensorProduct_trivializationAt_apply_snd
    (x₀ : B) (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ p).2 =
      TensorProduct.map
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 p.1).toLinearMap
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 p.1).toLinearMap
        p.2 := by
  rw [tensorProduct_trivializationAt]
  rfl

/-- Tensor-bundle analogue of the Hom-bundle `inCoordinates` map. -/
def inCoordinates
    (x₀ x : B) (y₀ y : B) (t : E₁ x ⊗[𝕜] E₂ y) : F₁ ⊗[𝕜] F₂ :=
  TensorProduct.map
    ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 x).toLinearMap
    ((trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y).toLinearMap
    t

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
     [∀ x : B, ContinuousAdd (E₁ x)] [∀ x : B, ContinuousSMul 𝕜 (E₁ x)]
     [∀ x : B, ContinuousAdd (E₂ x)] [∀ x : B, ContinuousSMul 𝕜 (E₂ x)] in
@[simp]
theorem inCoordinates_tmul
    (x₀ x : B) (y₀ y : B) (v : E₁ x) (w : E₂ y) :
    inCoordinates (𝕜 := 𝕜) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)
      x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 x v) ⊗ₜ[𝕜]
        ((trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y w) := by
  simp [inCoordinates, TensorProduct.map_tmul]

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_source (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).source =
      π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_target (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl



end Bundle.TensorProduct
