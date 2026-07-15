/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
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
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Pretrivialization
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

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
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T θ⟩).2 =
      (((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2)
        (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
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




end SmulByFun

/-!
## Equivalence of (0,0)-tensor fields and smooth scalar functions

A `C^n` scalar function `f : M → 𝕜` determines a `C^n` (0,0)-tensor field via the
isomorphism `𝕜 ≃ ContinuousMultilinearMap 𝕜 (Fin 0 → E) 𝕜` given by `constOfIsEmpty`,
and conversely a (0,0)-tensor field determines a scalar function by evaluation at
the unique empty argument. These two operations are inverses of each other.
-/


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


end
end Tensor0SBundle
