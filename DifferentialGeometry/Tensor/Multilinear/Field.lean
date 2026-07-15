/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Fiber

-- TODO: Rename MultilinearFields to MultilinearSections to give a more accurate description
-- and avoid conflict with algebraic fields.

/-!
# Smooth sections of the multilinear bundle

This file defines smooth sections of the multilinear bundle
`Bundle.continuousMultilinearMap 𝕜 s F E` over an arbitrary `C^n` vector bundle `E`,
and proves basic algebraic and analytic results about them.

These results generalize the `Tensor0SField` API from `RSTensor/Coordinates/Field.lean`,
which is the special case `E = TangentSpace I`.

## Main Definitions

* `MultilinearSection` : `C^n` sections of the `s`-multilinear bundle over `E`.
* `MultilinearSection.smulByFun` : pointwise scalar multiplication by a smooth function.
* `MultilinearSection.fromScalarField` : promote a `C^n` scalar function to a (0)-multilinear
  section via `constOfIsEmpty`.
* `MultilinearSection.toScalarField` : extract a scalar function from a (0)-multilinear section
  by evaluating at the empty tuple.

## Main Results

* `MultilinearSection.toScalarField_contMDiff` : the scalar function extracted from a `C^n`
  (0)-multilinear section is `C^n`.
* `MultilinearSection.toScalarField_fromScalarField` : round-trip identity.
* `MultilinearSection.fromScalarField_toScalarField` : round-trip identity.
* `MultilinearSection.toScalarField_add` : `toScalarField` is additive.
* `MultilinearSection.toScalarField_smulByFun` : `toScalarField` commutes with function smul.

## Tags

multilinear section, smooth section, vector bundle, multilinear bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

-- We follow the convention of Fiber.lean: use NormedAddCommGroup on fibers
-- (which provides TopologicalSpace), and do NOT add a separate [∀ x, TopologicalSpace (E x)]
-- to avoid topology diamonds with the FunLike instance.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Abbreviation for the model fiber of the `s`-multilinear bundle. -/
local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-!
## The type of smooth multilinear sections
-/

/-- A `C^n` section of the `s`-multilinear bundle over a vector bundle `E`.
This generalizes `Tensor0SField` from tangent bundles to arbitrary vector bundles. -/
abbrev MultilinearSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB] (s : ℕ) :=
  ContMDiffSection IB
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    n
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

namespace MultilinearSection

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

/-!
## Pointwise scalar multiplication by a smooth function
-/

/-- Pointwise scalar multiplication of a `C^n` multilinear section by a `C^n` scalar function
`φ : B → 𝕜` is again a `C^n` multilinear section.

This extends the constant-scalar `Module 𝕜` action on `ContMDiffSection` to the case of a
non-constant smooth multiplier. The smoothness of `φ x • α x` follows from
`ContMDiff.smul_section`. -/
def smulByFun {s : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s :=
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem smulByFun_apply {s : ℕ}
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    smulByFun n φ hφ α x = φ x • α x :=
  rfl

/-!
## Equivalence of (0)-multilinear sections and smooth scalar functions

A `C^n` scalar function `f : B → 𝕜` determines a `C^n` (0)-multilinear section via the
isomorphism `𝕜 ≃ ContinuousMultilinearMap 𝕜 (Fin 0 → E x) 𝕜` given by `constOfIsEmpty`,
and conversely a (0)-multilinear section determines a scalar function by evaluation at
the unique empty argument. These two operations are inverses of each other.
-/

/-- Promote a `C^n` scalar function `f : B → 𝕜` to a `C^n` (0)-multilinear section.
At each point `x`, the value is the constant continuous 0-multilinear map
`constOfIsEmpty (f x)`. -/
noncomputable def fromScalarField
    (f : B → 𝕜) (hf : ContMDiff IB 𝓘(𝕜) n f) :
    MultilinearSection 𝕜 F IB E n 0 :=
  ⟨fun x => ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => E x) (f x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    refine (contMDiff_multilinearSection_iff_coord E n b _).mpr fun σ x₀ => ?_

    have hcoord : ∀ x, (continuousMultilinearMap_basis b 0).repr
        (trivializationAt (MLF 0)
          (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀
          ⟨x, ContinuousMultilinearMap.constOfIsEmpty 𝕜
            (fun _ : Fin 0 => E x) (f x)⟩).2 σ = f x := by
      intro x
      simp_rw [continuousMultilinearMap_basis_repr]
      rfl
    simp_rw [hcoord]
    exact hf.contMDiffAt⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem fromScalarField_apply
    (f : B → 𝕜) (hf : ContMDiff IB 𝓘(𝕜) n f) (x : B)
    (v : Fin 0 → E x) :
    ((fromScalarField n f hf : MultilinearSection 𝕜 F IB E n 0).toFun x) v = f x :=
  ContinuousMultilinearMap.constOfIsEmpty_apply _ _ _ _

/-- Extract a scalar function from a (0)-multilinear section by evaluating at the empty tuple. -/
noncomputable def toScalarField
    (α : MultilinearSection 𝕜 F IB E n 0) : B → 𝕜 :=
  fun x => α.toFun x Fin.elim0

/-- The scalar function extracted from a `C^n` (0)-multilinear section is `C^n`. -/
theorem toScalarField_contMDiff
    (α : MultilinearSection 𝕜 F IB E n 0) :
    ContMDiff IB 𝓘(𝕜) n α.toScalarField := by
  let d := Module.finrank 𝕜 F
  let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
  have hα := ((contMDiff_multilinearSection_iff_coord E n b
    (fun x => (α.toFun x : Bundle.continuousMultilinearMap 𝕜 0 F E x))).mp α.contMDiff)
  intro x₀
  refine (hα Fin.elim0 x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (MLF 0)
    (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x _
  simp only [toScalarField]

  simp_rw [continuousMultilinearMap_basis_repr]

  exact congrArg (α.toFun x) (Subsingleton.elim _ _)

@[simp]
theorem toScalarField_fromScalarField
    (f : B → 𝕜) (hf : ContMDiff IB 𝓘(𝕜) n f) :
    toScalarField n (fromScalarField (F := F) (E := E) n f hf) = f := by
  ext x
  exact fromScalarField_apply n f hf x Fin.elim0

@[simp]
theorem fromScalarField_toScalarField
    (α : MultilinearSection 𝕜 F IB E n 0) :
    fromScalarField n (toScalarField n α) (toScalarField_contMDiff n α) = α := by
  apply ContMDiffSection.ext; intro x
  simp only [fromScalarField]
  apply Bundle.continuousMultilinearMap.ext; intro v
  show (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x)
    (α.toFun x Fin.elim0)) v = α.toFun x v
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  exact congrArg (α.toFun x) (Subsingleton.elim Fin.elim0 v)

set_option linter.unusedSectionVars false in
@[simp]
theorem toScalarField_add
    (α β : MultilinearSection 𝕜 F IB E n 0) :
    (α + β).toScalarField n = α.toScalarField n + β.toScalarField n := by
  ext x
  simp only [toScalarField, Pi.add_apply]
  show (α + β).toFun x Fin.elim0 = α.toFun x Fin.elim0 + β.toFun x Fin.elim0
  rw [show (α + β).toFun x = α.toFun x + β.toFun x from rfl]
  exact ContinuousMultilinearMap.add_apply _ _ _

set_option linter.unusedSectionVars false in
@[simp]
theorem toScalarField_smulByFun
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n 0) :
    (smulByFun n φ hφ α).toScalarField n = φ * α.toScalarField n := by
  ext x
  simp only [toScalarField, Pi.mul_apply]
  show (φ x • α.toFun x) Fin.elim0 = φ x * α.toFun x Fin.elim0
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]

end MultilinearSection

end
