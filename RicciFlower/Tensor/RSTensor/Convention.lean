import RicciFlower.Tensor.RSTensor.Components
import RicciFlower.Tensor.RSTensor.Contract

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

/-!
# Realized tensor slot conventions

This file is intentionally small.  It records the component and contraction
slot conventions used by higher geometry files, so those files do not unfold
the Hom implementation of `TensorRSSpace` or mention `basisTensor0S` directly.

Conventions fixed here:

* `componentRS basis T upper lower` means:
  evaluate the Hom tensor `T` on the covariant basis tensor selected by
  `upper`, then evaluate the output on the basis vectors selected by `lower`.
  In notation, this is `T(e^upper)(e_lower)`.
* `contract_trace r s x` contracts the first upper slot with the first lower
  slot of a `(1+r, s+1)` tensor.
* `contract_contravariant r s x alpha` contracts the first upper slot.  In the
  model formula the new covector is prepended by
  `model_tensorWithCovector_first`, not appended.

Keep this file as a convention checklist: documentation plus short simp
lemmas only.  Put real tensor algebra in `Components`, `Contract`, or a
dedicated auxiliary module.
-/

noncomputable section

namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open Bundle Module
open scoped Manifold ContDiff Topology BigOperators

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable [Module.Finite K E] [FiniteDimensional K E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners K E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {omega : WithTop ℕ∞} [IsManifold I omega M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Components

variable (basis : Module.Basis Idx K (TangentSpace I x))

/-- Convention lemma: mixed components are Hom evaluation on the basis covector
input and basis vector output. -/
@[simp]
theorem componentRS_basisTensor_apply {r s : Nat}
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) := by
  rfl

/-- Named `(1,1)` component convention. -/
@[simp]
theorem component11_apply
    (T : TensorRSSpace 1 1 I x) (i j : Idx) :
    componentRS (I := I) basis T (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) =
      (T (basisTensor0S (I := I) basis (fun _ : Fin 1 => i)))
        (fun _ : Fin 1 => basis j) := by
  rfl

/-- Named `(1,3)` component convention. -/
@[simp]
theorem component13_apply
    (T : TensorRSSpace 1 3 I x) (a i j k : Idx) :
    componentRS (I := I) basis T
        (fun _ : Fin 1 => a)
        (fun q : Fin 3 => if q = 0 then i else if q = 1 then j else k) =
      (T (basisTensor0S (I := I) basis (fun _ : Fin 1 => a)))
        (fun q : Fin 3 => if q = 0 then basis i else if q = 1 then basis j else basis k) := by
  rw [componentRS_apply]
  congr 1
  funext q
  by_cases h0 : q = 0
  · simp [h0]
  · by_cases h1 : q = 1
    · simp [h1]
    · simp [h0, h1]

/-- Named `(0,2)` component convention. -/
@[simp]
theorem component02_apply
    (A : Tensor0SSpace 2 I x) (i j : Idx) :
    component0S (I := I) basis A
        (fun q : Fin 2 => if q = 0 then i else j) =
      A (fun q : Fin 2 => if q = 0 then basis i else basis j) := by
  rw [component0S_apply]
  congr 1
  funext q
  by_cases h0 : q = 0 <;> simp [h0]

/-- Named `(0,4)` component convention. -/
@[simp]
theorem component04_apply
    (A : Tensor0SSpace 4 I x) (i j k l : Idx) :
    component0S (I := I) basis A
        (fun q : Fin 4 => if q = 0 then i else if q = 1 then j else if q = 2 then k else l) =
      A (fun q : Fin 4 =>
        if q = 0 then basis i else if q = 1 then basis j else if q = 2 then basis k else basis l) := by
  rw [component0S_apply]
  congr 1
  funext q
  by_cases h0 : q = 0
  · simp [h0]
  · by_cases h1 : q = 1
    · simp [h1]
    · by_cases h2 : q = 2
      · simp [h2]
      · simp [h0, h1, h2]

end Components

section Contractions

/-- Model convention behind `contract_trace`: the trace contracts the first
upper slot with the first lower slot. -/
@[simp]
theorem model_contract_trace_first_upper_first_lower_apply
    (r s : Nat) (T : TensorRSModel (1 + r) (s + 1) K E) :
    model_contract_trace (𝕜 := K) (E := E) r s T =
      ∑ i : Fin (Module.finrank K E),
        (model_contract_covariant_bilinear
          (𝕜 := K) (E := E) r s
          ((Module.finBasis K E) i))
          ((model_contract_contravariant_first_bilinear
            (𝕜 := K) (E := E) r (s + 1)
            (model_covectorOfCLM (𝕜 := K) (E := E)
              ((Module.finBasis K E).cDualBasis i))) T) := by
  exact model_contract_trace_apply (𝕜 := K) (E := E) r s T

/-- Model convention behind `contract_contravariant`: the covector is placed in
the first contravariant slot, before the existing `r` upper slots. -/
@[simp]
theorem contract_contravariant_first_model_apply
    {r : Nat} (alpha : Tensor0SModel 1 K E) (beta : Tensor0SModel r K E)
    (v : Fin (1 + r) -> E) :
    model_tensorWithCovector_first (𝕜 := K) (E := E) r alpha beta v =
      alpha (v ∘ Fin.castAdd r) * beta (v ∘ Fin.natAdd 1) := by
  change Bundle.continuousMultilinearMap.modelProduct 1 r alpha beta v =
    alpha (v ∘ Fin.castAdd r) * beta (v ∘ Fin.natAdd 1)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]

end Contractions

end Tensor0SBundle
