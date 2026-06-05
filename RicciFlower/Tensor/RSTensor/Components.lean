import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.Multilinear.Tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Pointwise tensor components

This file provides component maps and extensionality for the realized Hom model
`TensorRSSpace r s I x = Tensor0SSpace r I x ->L Tensor0SSpace s I x`.
-/

noncomputable section

namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Covariant

variable {s q : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

@[simp]
theorem component0S_add
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A + B) slots =
      component0S (I := I) basis A slots + component0S (I := I) basis B slots := by
  rfl

@[simp]
theorem component0S_smul
    (c : 𝕜) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (c • A) slots =
      c * component0S (I := I) basis A slots := by
  rfl

/-- Component theorem for the pointwise product of covariant tensors. -/
theorem component0S_product
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (slots : Fin (s + q) -> Idx) :
    component0S (I := I) basis
        (Bundle.continuousMultilinearMap.product_fun A B) slots =
      component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
        component0S (I := I) basis B (slots ∘ Fin.natAdd s) := by
  rw [component0S_apply, Bundle.continuousMultilinearMap.product_fun_apply]
  rfl

/-- Permute the slots of a covariant tensor at one point. -/
def permute0S
    (σ : Fin s ≃ Fin s) (A : Tensor0SSpace s I x) : Tensor0SSpace s I x :=
  A.domDomCongr σ

@[simp]
theorem component0S_permute0S
    (σ : Fin s ≃ Fin s) (A : Tensor0SSpace s I x)
    (slots : Fin s -> Idx) :
    component0S (I := I) basis (permute0S (I := I) σ A) slots =
      component0S (I := I) basis A (slots ∘ σ) := by
  rw [component0S_apply, component0S_apply]
  simp [permute0S]

end Covariant

section Mixed

variable {r s : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

/-- Conventional component of a mixed tensor in the Hom model.

The `upper` indices select the covariant basis tensor used as Hom input; the
`lower` indices evaluate the covariant output on basis vectors. -/
def componentRS
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 :=
  component0S (I := I) basis (T (basisTensor0S (I := I) basis upper)) lower

/-- Reconstruct a mixed tensor from its `componentRS` coordinate table. -/
noncomputable def ofComponentsRS
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (r s : Nat)
    (c : (Fin r -> Idx) -> (Fin s -> Idx) -> 𝕜) :
    TensorRSSpace r s I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun input =>
        (coordEquiv0S (I := I) basis s).symm
          (fun lower => ∑ upper : Fin r -> Idx,
            component0S (I := I) basis input upper * c upper lower)
      map_add' := by
        intro A B
        apply (coordEquiv0S (I := I) basis s).injective
        ext lower
        rw [LinearEquiv.apply_symm_apply]
        rw [map_add]
        rw [LinearEquiv.apply_symm_apply]
        rw [LinearEquiv.apply_symm_apply]
        simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro a A
        apply (coordEquiv0S (I := I) basis s).injective
        ext lower
        rw [LinearEquiv.apply_symm_apply]
        rw [map_smul]
        rw [LinearEquiv.apply_symm_apply]
        simp [Finset.mul_sum, mul_assoc] }

@[simp]
theorem componentRS_ofComponentsRS
    (c : (Fin r -> Idx) -> (Fin s -> Idx) -> 𝕜)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis
      (ofComponentsRS (I := I) basis r s c) upper lower = c upper lower := by
  unfold componentRS ofComponentsRS
  change component0S (I := I) basis
      ((coordEquiv0S (I := I) basis s).symm
        (fun lower => ∑ upper' : Fin r -> Idx,
          component0S (I := I) basis
            (basisTensor0S (I := I) basis upper) upper' * c upper' lower))
      lower = c upper lower
  have hcoord := congrFun
    ((coordEquiv0S (I := I) basis s).apply_symm_apply
      (fun lower => ∑ upper' : Fin r -> Idx,
        component0S (I := I) basis
          (basisTensor0S (I := I) basis upper) upper' * c upper' lower)) lower
  rw [coordEquiv0S_apply] at hcoord
  have hsum :
      (∑ upper' : Fin r -> Idx,
        component0S (I := I) basis
          (basisTensor0S (I := I) basis upper) upper' * c upper' lower) =
        c upper lower := by
    have hdelta :
        (∑ upper' : Fin r -> Idx,
          (if upper = upper' then (1 : 𝕜) else 0) * c upper' lower) =
          c upper lower := by
      rw [Finset.sum_eq_single upper]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    calc
      (∑ upper' : Fin r -> Idx,
        component0S (I := I) basis
          (basisTensor0S (I := I) basis upper) upper' * c upper' lower) =
          (∑ upper' : Fin r -> Idx,
            (if upper = upper' then (1 : 𝕜) else 0) * c upper' lower) := by
            refine Finset.sum_congr rfl fun upper' _ => ?_
            change component0S (I := I) basis
                (basisTensor0S (I := I) basis upper) upper' * c upper' lower =
              (if upper = upper' then (1 : 𝕜) else 0) * c upper' lower
            rw [basisTensor0S_component]
      _ = c upper lower := hdelta
  exact hcoord.trans hsum

@[simp]
theorem componentRS_apply
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem componentRS_smul
    (c : 𝕜) (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis (c • T) upper lower =
      c * componentRS (I := I) basis T upper lower := by
  unfold componentRS
  simp

/-- Scalar multiplication of a mixed tensor through the canonical model
equivalence.  This avoids downstream dependence on the reducible
`ContinuousLinearMap` representation of `TensorRSSpace`. -/
def smulRS (c : 𝕜) (T : TensorRSSpace r s I x) :
    TensorRSSpace r s I x :=
  TensorRSSpace.ofModel (I := I) (x := x) (c • TensorRSSpace.toModel (I := I) T)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem componentRS_smulRS
    (c : 𝕜) (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis (smulRS (I := I) c T) upper lower =
      c * componentRS (I := I) basis T upper lower := by
  unfold componentRS smulRS
  unfold TensorRSSpace.ofModel
  rw [tensorRSSpace_continuousLinearEquiv_symm_apply_apply]
  rw [ContinuousLinearMap.smul_apply]
  rw [TensorRSSpace.toModel]
  rw [tensorRSSpace_continuousLinearEquiv_apply_apply]
  rw [← Tensor0SSpace.toModel_smul]
  rw [Tensor0SSpace.ofModel_toModel]
  rw [component0S_smul]

/-- Expanding the Hom input of a mixed tensor in a basis gives the usual
component contraction formula. -/
theorem componentRS_apply_input_eq_sum
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x)
    (lower : Fin s -> Idx) :
    component0S (I := I) basis (T input) lower =
      ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRS (I := I) basis T upper lower := by
  have hinput :
      (∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper • basisTensor0S (I := I) basis upper) =
        input := by
    simpa [basisTensor0S] using (tensor0SBasis (I := I) basis r).sum_repr input
  calc
    component0S (I := I) basis (T input) lower =
        component0S (I := I) basis
          (T (∑ upper : Fin r -> Idx,
            component0S (I := I) basis input upper •
              basisTensor0S (I := I) basis upper)) lower := by
          rw [hinput]
    _ = ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRS (I := I) basis T upper lower := by
          let inputSum : Tensor0SSpace r I x :=
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper •
                basisTensor0S (I := I) basis upper
          change component0S (I := I) basis (T inputSum) lower =
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper *
                componentRS (I := I) basis T upper lower
          rw [← congrFun (coordMap0S_apply (I := I) basis (T inputSum)) lower]
          dsimp [inputSum]
          rw [map_sum]
          simp [map_smul]

/-- Extensionality for mixed tensors from equality of all Hom-model components. -/
theorem extRS_basis
    {A B : TensorRSSpace r s I x}
    (h : ∀ upper : Fin r -> Idx, ∀ lower : Fin s -> Idx,
      componentRS (I := I) basis A upper lower =
        componentRS (I := I) basis B upper lower) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro input
  apply ext0S_basis (I := I) basis
  intro lower
  rw [componentRS_apply_input_eq_sum (I := I) basis A input lower,
    componentRS_apply_input_eq_sum (I := I) basis B input lower]
  refine Finset.sum_congr rfl fun upper _ => ?_
  rw [h upper lower]

end Mixed

end Tensor0SBundle
