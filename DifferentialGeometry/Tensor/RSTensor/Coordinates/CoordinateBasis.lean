import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointwise tensor coordinates from a tangent basis

This file is the metric-free coordinate core for realized tensor fibers.  The
primitive algebraic object is a pointwise `Module.Basis` of one tangent fiber;
local-frame coordinates should pass through `IsLocalFrameOn.toBasisAt`.
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

section ModelBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The covector dual to a vector-space basis element, as a continuous linear map. -/
def coframeOfBasis (basis : Module.Basis Idx 𝕜 V) (i : Idx) : V →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap (basis.coord i)

@[simp]
theorem coframeOfBasis_apply (basis : Module.Basis Idx 𝕜 V) (i : Idx) (v : V) :
    coframeOfBasis basis i v = basis.coord i v :=
  rfl

/-- The covariant tensor basis element indexed by `slots : Fin s -> Idx`.

It is the tensor product of the coordinate covectors:
`v ↦ ∏ a, basis.coord (slots a) (v a)`. -/
def continuousMultilinearMapBasisElem
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) (slots : Fin s -> Idx) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜 :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun a => coframeOfBasis basis (slots a))

@[simp]
theorem continuousMultilinearMapBasisElem_apply
    (basis : Module.Basis Idx 𝕜 V) (s : Nat)
    (slots slots' : Fin s -> Idx) :
    continuousMultilinearMapBasisElem basis s slots (fun a => basis (slots' a)) =
      if slots = slots' then 1 else 0 := by
  classical
  simp_rw [continuousMultilinearMapBasisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    coframeOfBasis_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases h : slots = slots'
  · subst h
    simp
  · simp only [h, ite_false]
    have ⟨a, ha⟩ : ∃ a, slots a ≠ slots' a := by
      contrapose! h
      exact funext h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg (Ne.symm ha))

/-- Linear independence of the coordinate covariant tensor basis. -/
theorem continuousMultilinearMapBasisElem_linearIndependent
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) :
    LinearIndependent 𝕜 (continuousMultilinearMapBasisElem basis s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc slots'
  have h1 : (∑ slots : Fin s -> Idx,
      c slots • continuousMultilinearMapBasisElem basis s slots)
      (fun a => basis (slots' a)) = 0 := by
    rw [hc]
    rfl
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    continuousMultilinearMapBasisElem_apply] at h1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rwa [smul_eq_mul, mul_one] at h1

/-- The coordinate covariant tensor basis induced by a basis of `V`. -/
def continuousMultilinearMapBasis
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) :
    Module.Basis (Fin s -> Idx) 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜) :=
  Module.Basis.mk (continuousMultilinearMapBasisElem_linearIndependent basis s)
    ((continuousMultilinearMapBasisElem_linearIndependent basis s).span_eq_top_of_card_eq_finrank'
      (by
        have hdim : Module.finrank 𝕜 V = Fintype.card Idx := by
          rw [Module.finrank_eq_card_basis basis]
        rw [Fintype.card_fun, Fintype.card_fin,
          finrank_continuousMultilinearMap (𝕜 := 𝕜) (F := V), hdim])).ge

theorem continuousMultilinearMapBasis_apply
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) (slots : Fin s -> Idx) :
    continuousMultilinearMapBasis basis s slots =
      continuousMultilinearMapBasisElem basis s slots :=
  congr_fun (Module.Basis.coe_mk
    (continuousMultilinearMapBasisElem_linearIndependent basis s) _) slots

/-- The coordinate of a multilinear map in the induced tensor basis is evaluation
on the corresponding tuple of basis vectors. -/
theorem continuousMultilinearMapBasis_repr
    (basis : Module.Basis Idx 𝕜 V) (s : Nat)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜)
    (slots : Fin s -> Idx) :
    (continuousMultilinearMapBasis basis s).repr A slots =
      A (fun a => basis (slots a)) := by
  conv_rhs => rw [← (continuousMultilinearMapBasis basis s).sum_repr A]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, continuousMultilinearMapBasis_apply,
    continuousMultilinearMapBasisElem_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ModelBasis

section Tensor0S

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {s : Nat} {x : M}

/-- The pointwise covariant tensor basis induced by a tangent basis. -/
def tensor0SBasis (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Module.Basis (Fin s -> Idx) 𝕜 (Tensor0SSpace s I x) :=
  continuousMultilinearMapBasis basis s

/-- The covariant basis tensor indexed by `slots`. -/
def basisTensor0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (slots : Fin s -> Idx) :
    Tensor0SSpace s I x :=
  tensor0SBasis (I := I) basis s slots

/-- Component of a pointwise covariant tensor in a tangent basis. -/
def component0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) : 𝕜 :=
  A (fun a => basis (slots a))

@[simp]
theorem component0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis A slots = A (fun a => basis (slots a)) :=
  rfl

/-- Rewrite the slot map of a covariant component under a slot-map equality, without
unfolding `component0S` / `Fin.cons`.  Lets downstream proofs prove `slots = slots'` separately
(e.g. by `funext`) and rewrite, instead of relying on `backward.isDefEq.respectTransparency false`. -/
theorem component0S_congr_slots
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) {slots slots' : Fin s -> Idx}
    (h : slots = slots') :
    component0S (I := I) basis A slots = component0S (I := I) basis A slots' := by
  rw [h]

@[simp]
theorem tensor0SBasis_repr
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    (tensor0SBasis (I := I) basis s).repr A slots =
      component0S (I := I) basis A slots := by
  exact continuousMultilinearMapBasis_repr basis s A slots

/-- Linear coordinate map for a covariant tensor fiber in a tangent basis. -/
def coordMap0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Tensor0SSpace s I x →ₗ[𝕜] ((Fin s -> Idx) -> 𝕜) :=
  ((tensor0SBasis (I := I) basis s).equivFun).toLinearMap

@[simp]
theorem coordMap0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) :
    coordMap0S (I := I) basis s A = component0S (I := I) basis A := by
  ext slots
  change (tensor0SBasis (I := I) basis s).repr A slots =
    component0S (I := I) basis A slots
  exact tensor0SBasis_repr (I := I) basis A slots

/-- Linear coordinate equivalence for a covariant tensor fiber in a tangent basis. -/
def coordEquiv0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[𝕜] ((Fin s -> Idx) -> 𝕜) :=
  (tensor0SBasis (I := I) basis s).equivFun

@[simp]
theorem coordEquiv0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) :
    coordEquiv0S (I := I) basis s A = component0S (I := I) basis A := by
  ext slots
  change (tensor0SBasis (I := I) basis s).repr A slots =
    component0S (I := I) basis A slots
  exact tensor0SBasis_repr (I := I) basis A slots

/-- Extensionality for covariant tensors from equality of all basis components. -/
theorem ext0S_basis
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    {A B : Tensor0SSpace s I x}
    (h : ∀ slots : Fin s -> Idx,
      component0S (I := I) basis A slots = component0S (I := I) basis B slots) :
    A = B := by
  apply (coordEquiv0S (I := I) basis s).injective
  ext slots
  simpa using h slots

theorem basisTensor0S_component
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (slots slots' : Fin s -> Idx) :
    component0S (I := I) basis (basisTensor0S (I := I) basis slots) slots' =
      if slots = slots' then 1 else 0 := by
  change (continuousMultilinearMapBasis basis s slots) (fun a => basis (slots' a)) =
    if slots = slots' then 1 else 0
  rw [continuousMultilinearMapBasis_apply]
  exact continuousMultilinearMapBasisElem_apply basis s slots slots'

end Tensor0S

end Tensor0SBundle
