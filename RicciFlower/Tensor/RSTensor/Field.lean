/-
Authors: Yuan Liao, Jack McCarthy
-/
import RicciFlower.Tensor.RSTensor.Defs
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.Product.Defs
import RicciFlower.Tensor.Multilinear.Basis
import RicciFlower.Tensor.Multilinear.Tensor

/-!
# Smooth Tensor Fields on Manifolds

This file defines smooth tensor fields on a smooth manifold `M`.

## Main Definitions

* `TensorRSField r s` : `C^n` (r,s)-tensor fields on `M`, i.e. `C^n` sections of the
  (r,s)-tensor bundle `TensorRSSpace r s I`.
* `Tensor0SField s` : `C^n` (0,s)-tensor fields on `M`, i.e. `C^n` sections of the
  (0,s)-tensor bundle `Tensor0SSpace s I`.

## Tags

tensor field, smooth section, smooth manifold, vector space
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-!
## Manifold tensor fields (sections of the bundle)
-/

/-- A `C^n` (r,s)-tensor field on `M`: a `C^n` section of the (r,s)-tensor bundle. -/
abbrev TensorRSField (r s : ℕ) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

/-- A `C^n` (0,s)-tensor field on `M`: a `C^n` section of the (0,s)-tensor bundle. -/
abbrev Tensor0SField (s : ℕ) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiffSection I
    (Tensor0SModel s 𝕜 E)
    n
    (fun x : M => Tensor0SSpace s I x)

section ApplyInput

variable {r s : ℕ} [CompleteSpace 𝕜]

/-- Model-level evaluation of a mixed tensor on a covariant tensor input,
packaged as a continuous bilinear map. -/
noncomputable def model_applyInput_bilinear (r s : ℕ) :
    Tensor0SModel r 𝕜 E →L[𝕜]
      (TensorRSModel r s 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.id 𝕜 (TensorRSModel r s 𝕜 E))

@[simp]
theorem model_applyInput_bilinear_apply (r s : ℕ)
    (θ : Tensor0SModel r 𝕜 E) (T : TensorRSModel r s 𝕜 E) :
    model_applyInput_bilinear (𝕜 := 𝕜) (E := E) r s θ T = T θ := rfl

/-- Fixed-trivialization model identity for evaluating a mixed tensor on a
covariant input. -/
theorem tensor0SModelAt_applyInput_eq
    (r s : ℕ) {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T θ⟩).2 =
      (((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2)
        (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) := by
  ext v
  rw [Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s hx]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r s hx]
  have hθ :
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
        (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) = θ := by
    have hcoord :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt 𝕜 x θ =
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      exact congrFun ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx) θ
    rw [← hcoord]
    exact (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx θ
  rw [hθ]

/-- Pointwise evaluation of a mixed tensor field on a covariant tensor field. -/
noncomputable def tensorRSField_applyInput_fun
    (T : (x : M) ->
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x :=
  fun x => T x (θ x)

/-- Evaluating a smooth mixed tensor field on a smooth covariant tensor input
gives a smooth covariant tensor field. -/
noncomputable def tensorRSField_applyInput
    (T : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (θ : Tensor0SField n r (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨tensorRSField_applyInput_fun (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) (r := r) (s := s) (fun x => T x) (fun x => θ x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hθ := θ.contMDiff x₀
  rw [contMDiffAt_section] at hθ
  have hcombine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x : M =>
          model_applyInput_bilinear (𝕜 := 𝕜) (E := E) r s
            (((trivializationAt (Tensor0SModel r 𝕜 E)
                (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ x⟩).2)
            (((trivializationAt (TensorRSModel r s 𝕜 E)
                (fun x => TensorRSSpace r s I x) x₀) ⟨x, T x⟩).2)) x₀ := by
    exact ((contMDiffAt_const
      (c := model_applyInput_bilinear (𝕜 := 𝕜) (E := E) r s)).clm_apply hθ).clm_apply hT
  refine hcombine.congr_of_eventuallyEq ?_
  filter_upwards
    [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
  exact tensor0SModelAt_applyInput_eq (𝕜 := 𝕜) (E := E) (I := I)
    (M := M) r s hx (T x) (θ x)

@[simp]
theorem tensorRSField_applyInput_apply
    (T : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (θ : Tensor0SField n r (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n T θ x = T x (θ x) := by
  simp [tensorRSField_applyInput, tensorRSField_applyInput_fun]

end ApplyInput

/-!
## Manifold tensor fields: addition and smooth-function scalar multiplication

Addition and constant-scalar smul are inherited directly from `ContMDiffSection` (which is an
`AddCommGroup` and a `𝕜`-module).  We additionally provide pointwise smul by a smooth function
`φ : M → 𝕜`.
-/

section SmulByFun

variable {r s : ℕ} [CompleteSpace 𝕜]

-- RS bundle instance synthesis for `smul_section` is expensive.
/-- Pointwise scalar multiplication of a `C^n` (r,s)-tensor field by a `C^n` scalar function
`φ : M → 𝕜` is again a `C^n` (r,s)-tensor field.

This extends the constant-scalar `Module 𝕜` action on `ContMDiffSection` to the case of a
non-constant smooth multiplier. The smoothness of `φ x • α x` follows from
`ContMDiff.smul_section`. -/
def tensorRSField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨fun x => φ x • α x, by
    letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    intro x₀
    rw [contMDiffAt_section]
    have hα := α.contMDiff x₀
    rw [contMDiffAt_section] at hα
    set e := trivializationAt (TensorRSModel r s 𝕜 E) (fun x => TensorRSSpace r s I x) x₀
    refine ((hφ x₀).smul hα).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))
      fun x hx => (e.linear 𝕜 hx).2 _ _⟩

@[simp]
theorem tensorRSField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensorRSField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

/-- Pointwise scalar multiplication of a `C^n` (0,s)-tensor field by a `C^n` scalar function
`φ : M → 𝕜` is again a `C^n` (0,s)-tensor field. -/
def tensor0SField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

@[simp]
theorem tensor0SField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensor0SField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

end SmulByFun

/-!
## Equivalence of (0,0)-tensor fields and smooth scalar functions

A `C^n` scalar function `f : M → 𝕜` determines a `C^n` (0,0)-tensor field via the
isomorphism `𝕜 ≃ ContinuousMultilinearMap 𝕜 (Fin 0 → E) 𝕜` given by `constOfIsEmpty`,
and conversely a (0,0)-tensor field determines a scalar function by evaluation at
the unique empty argument. These two operations are inverses of each other.
-/

/-- Promote a `C^n` scalar function `f : M → 𝕜` to a `C^n` (0,0)-tensor field.
At each point `x`, the value is the constant continuous 0-multilinear map `constOfIsEmpty (f x)`. -/
noncomputable def Tensor0SField.fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  ⟨fun x => ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (f x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) n b _).mpr
      fun σ x₀ => ?_
    -- The trivialized coordinate of constOfIsEmpty at σ : Fin 0 → Fin d is just the scalar
    have hcoord : ∀ x, (continuousMultilinearMap_basis b 0).repr
        (trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun x => Tensor0SSpace 0 I x) x₀
          ⟨x, ContinuousMultilinearMap.constOfIsEmpty 𝕜
            (fun _ : Fin 0 => TangentSpace I x) (f x)⟩).2 σ = f x := by
      intro x
      simp_rw [continuousMultilinearMap_basis_repr]
      rfl
    simp_rw [hcoord]
    exact hf.contMDiffAt⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.fromScalarField_apply [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) (x : M) (v : Fin 0 → TangentSpace I x) :
    Tensor0SSpace.toModel (Tensor0SField.fromScalarField n f hf x) v = f x := by
  unfold Tensor0SField.fromScalarField Tensor0SSpace.toModel tensor0SSpace_continuousLinearEquiv
  exact ContinuousMultilinearMap.constOfIsEmpty_apply _ _ _ _

/-- The constant unit `(0,0)` tensor field. -/
noncomputable def Tensor0SField.one0 [CompleteSpace 𝕜] :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  Tensor0SField.fromScalarField n (fun _ : M => (1 : 𝕜)) contMDiff_const

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.one0_apply [CompleteSpace 𝕜]
    (x : M) (v : Fin 0 → TangentSpace I x) :
    Tensor0SSpace.toModel (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x) v = (1 : 𝕜) := by
  exact Tensor0SField.fromScalarField_apply n (fun _ : M => (1 : 𝕜))
    contMDiff_const x v

/-!
A `C^n` (0,0)-tensor field `α` determines a `C^n` scalar function by evaluating each fiber
element (a 0-multilinear map, i.e. essentially a scalar) at the unique empty argument.
-/

/-- Extract a scalar function from a (0,0)-tensor field by evaluating at the empty tuple. -/
noncomputable def Tensor0SField.toScalarField
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  fun x => Tensor0SSpace.toModel (α x) Fin.elim0

set_option linter.unusedSectionVars false in
/-- The scalar function extracted from a `C^n` (0,0)-tensor field is `C^n`. -/
theorem Tensor0SField.toScalarField_contMDiff [CompleteSpace 𝕜]
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n α.toScalarField := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
    (fun x => (α x : Tensor0SSpace 0 I x))).mp α.contMDiff)
  intro x₀
  refine (hα Fin.elim0 x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (Tensor0SModel 0 𝕜 E)
    (fun x => Tensor0SSpace 0 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  -- Any (0,0)-tensor is constOfIsEmpty of its scalar value
  have hα_const : α x = ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (Tensor0SField.toScalarField n α x) := by
    ext v
    -- Unfold the equiv (= id) wrapping both sides, then constOfIsEmpty_apply
    simp only [tensor0SSpace_continuousLinearEquiv, ContinuousLinearEquiv.coe_mk,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id,
      Tensor0SField.toScalarField, Tensor0SSpace.toModel]
    -- Goal: (α x) v = (constOfIsEmpty 𝕜 _ ((α x) Fin.elim0)) v
    -- constOfIsEmpty c v = c definitionally, so RHS = (α x) Fin.elim0 = (α x) applied to Fin.elim0
    change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) v =
      DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) Fin.elim0
    exact congrArg _ (Subsingleton.elim v Fin.elim0)
  simp only [Tensor0SField.toScalarField]
  conv_rhs => rw [hα_const]
  simp_rw [continuousMultilinearMap_basis_repr]
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.toScalarField_fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField.toScalarField n (Tensor0SField.fromScalarField n f hf) = f := by
  ext x
  exact Tensor0SField.fromScalarField_apply n f hf x Fin.elim0

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.fromScalarField_toScalarField [CompleteSpace 𝕜]
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.fromScalarField n (Tensor0SField.toScalarField n α)
      (Tensor0SField.toScalarField_contMDiff n α) = α := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  apply ContMDiffSection.ext; intro x
  -- LHS = constOfIsEmpty 𝕜 _ (toScalarField n α x), need to show = α x
  simp only [Tensor0SField.fromScalarField]
  -- α x = constOfIsEmpty 𝕜 _ (toScalarField n α x)
  symm; ext v
  simp only [tensor0SSpace_continuousLinearEquiv, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, id,
    Tensor0SField.toScalarField, Tensor0SSpace.toModel]
  change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) v =
    DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) Fin.elim0
  exact congrArg _ (Subsingleton.elim v Fin.elim0)

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.toScalarField_add [CompleteSpace 𝕜]
    (α β : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (α + β).toScalarField n = α.toScalarField n + β.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, Pi.add_apply]
  -- Goal: ((α + β) x).toModel Fin.elim0 = (α x).toModel Fin.elim0 + (β x).toModel Fin.elim0
  rw [show (α + β) x = α x + β x from rfl, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in
@[simp]
theorem Tensor0SField.toScalarField_smulByFun [CompleteSpace 𝕜]
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (tensor0SField_smulByFun n φ hφ α).toScalarField n = φ * α.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, tensor0SField_smulByFun_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Pi.mul_apply, smul_eq_mul]

/-!
## Embedding (0,s)-tensor fields as (0,s)-valued TensorRS fields  (DEAD CODE — no callers)

A `Tensor0SSpace s I x` element `T` embeds into `TensorRSSpace 0 s I x`
(= `Tensor0SSpace 0 I x →L[𝕜] Tensor0SSpace s I x`) by sending
`c ↦ (toModel c Fin.elim0) • T`, i.e. extracting the scalar from the
(0,0)-tensor `c` and scaling `T`.

This old specialized sketch is not kept as commented Lean code, because it is
easy for stub audits to mistake it for an active obligation. The live general
version is `MixedSection.fromMultilinearSection` in `RicciFlower.Tensor.Mixed.Field`:
it constructs the same fiberwise map
`c ↦ (eval₀ x c) • T` and proves smoothness by trivializing both multilinear
bundles, reducing the `0`-multilinear coordinate to evaluation at `Fin.elim0`,
and applying a constant `ContinuousLinearMap.smulRightL` to the smooth
multilinear section.
-/

end
end Tensor0SBundle

/-!
## Tensor product of (0,s)-tensor fields
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
variable {s q : ℕ}

variable (n : WithTop ℕ∞)

/-- The tensor product of a `C^n` (0,s)-tensor field `α` and a `C^n` (0,q)-tensor field `β`
is a `C^n` (0,s+q)-tensor field, defined pointwise by `tensor0S_product_fun`.

Smoothness is proved by reducing to basis coordinates via
`contMDiff_multilinearSection_iff_coord`: the trivialized coordinate of `α ⊗ β` at
`σ : Fin (s+q) → Fin d` equals the product of the coordinate of `α` at `σ ∘ Fin.castAdd q`
and the coordinate of `β` at `σ ∘ Fin.natAdd s`, both of which are smooth. -/
noncomputable def tensor0SField_product
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (β : Tensor0SField n q (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n (s + q) (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + q)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) q
  ⟨fun x => (α x).product_fun (β x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    rw [contMDiff_multilinearSection_iff_coord (TangentSpace I) n b]
    intro σ x₀
    -- Extract coordinate smoothness of α and β
    have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (α x : Tensor0SSpace s I x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (β x : Tensor0SSpace q I x))).mp β.contMDiff)
    -- Rewrite the coordinate of the product as a product of coordinates
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

end
end Tensor0SBundle
