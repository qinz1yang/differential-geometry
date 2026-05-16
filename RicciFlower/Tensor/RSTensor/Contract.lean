/-
Authors: Yuan Liao, Jack McCarthy
-/
import RicciFlower.Tensor.RSTensor.Defs
import RicciFlower.Tensor.Multilinear.Curry
import RicciFlower.Tensor.Multilinear.Tensor
import RicciFlower.Tensor.RSTensor.Field
import RicciFlower.Tensor.Auxiliary.Basis
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Trace
/-!
# Interior Product and Contraction of Tensors

This file defines the interior product (contraction with a tangent vector) and contraction
with a cotangent vector (1-form) for mixed tensors at a point of a smooth manifold.

## Main Definitions

* `interior_product s x v` : contraction of a (0,s+1)-tensor with a tangent vector `v`,
  giving a (0,s)-tensor by feeding `v` into the first slot.
* `contract_covariant r s x v` : contraction of an (r,s+1)-tensor with a tangent vector,
  giving an (r,s)-tensor by post-composing with `interior_product`.
* `contract_contravariant r s x α` : contraction of an (r+1,s)-tensor with a cotangent
  vector `α`, giving an (r,s)-tensor by pre-composing with tensoring with `α`.
* `contract_Tensor0SField_fun s α X` : pointwise contraction of a (0,s+1)-tensor field
  with a vector field, giving a (0,s)-tensor field.
* `contract_Tensor0SField s α X` : contraction of a smooth (0,s+1)-tensor field
  with a smooth vector field (a `ContMDiffSection` of the tangent bundle),
  yielding a smooth (0,s)-tensor field.

## Tags

interior product, contraction, cotangent, tensor, smooth manifold
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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-!
## Model-level interior product

The pointwise interior product works at the model fiber level first. This is a pure
`NormedSpace`-level construction (currying + applying a vector), which we transport
to the bundle fiber via `tensor0SSpace_continuousLinearEquiv`.
-/

/-- The model-level interior product: given a vector `v : E`, contract a (0,s+1)-tensor
model fiber with `v` in its first slot. This is currying-then-applying. -/
noncomputable def model_interior_product (s : ℕ) (v : E) :
    Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  (ContinuousLinearMap.apply 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

/-- The model-level interior product, packaged as a continuous bilinear map in the
vector argument and the (0,s+1)-tensor argument. Used to prove smoothness of the
interior-product field operation. -/
noncomputable def model_interior_bilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] (s : ℕ) :
    E →L[𝕜] (Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

set_option linter.unusedSectionVars false in
theorem model_interior_bilinear_apply (s : ℕ) (v : E) (T : Tensor0SModel (s + 1) 𝕜 E) :
    model_interior_bilinear 𝕜 E s v T = model_interior_product s v T := rfl

/-!
## Interior product
-/

/-- Contraction of a (0,s+1)-tensor with a tangent vector `v`, giving a (0,s)-tensor
by feeding `v` into the first slot via the curry-left isomorphism. -/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm.toContinuousLinearMap.comp
    ((model_interior_product s (v : E)).comp
      (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).toContinuousLinearMap)

/-!
## Model-level tensor-with-covector embedding

Given a model-level (0,1)-tensor `α`, the map `β ↦ β ⊗ α` is a continuous linear map
`(0,r) →L (0,r+1)`. We build it as a linear map using `modelProduct` and promote to a
continuous linear map via finite-dimensionality.
-/

/-- The model-level embedding `β ↦ β ⊗ α : (0,r) →L (0,r+1)`, given a (0,1)-tensor `α`. -/
noncomputable def model_tensorWithCovector (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct r 1 β α
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply, add_mul]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def model_tensorWithCovector_first (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply, mul_add]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- The curry `α ↦ (β ↦ α ⊗ β)` as a continuous bilinear map, with `α` in slot 0. -/
noncomputable def model_tensorWithCovector_first_bilinear (r : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        LinearMap.toContinuousLinearMap
          { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
            map_add' := fun β₁ β₂ => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.add_apply, mul_add]
            map_smul' := fun c β => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }
      map_add' := fun α₁ α₂ => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply, add_mul]
      map_smul' := fun c α => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }

set_option linter.unusedSectionVars false in
theorem model_tensorWithCovector_first_bilinear_apply (r : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (β : Tensor0SModel r 𝕜 E) :
    model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r α β =
      model_tensorWithCovector_first r α β := rfl

/-!
## Contraction of smooth tensor fields

We lift the pointwise `interior_product` to tensor fields: contracting a smooth
(0,s+1)-tensor field with a smooth vector field produces a smooth (0,s)-tensor field.
This corresponds to the standard result that contraction of a (0,s)-tensor field with
a smooth vector field yields a (0,s−1)-tensor field, using the Lean indexing
convention `s + 1 → s`.
-/

/-!
## Model-level bilinear contractions on `TensorRSModel`

For smoothness of field-level contractions of `TensorRSField`, we package the fiber-level
`contract_covariant` and `contract_contravariant_first` as continuous bilinear maps in their
contraction-vector / contraction-covector argument. -/

/-- Model-level bilinear contraction covariant: pairs a vector with a `(r, s+1)`-tensor to
produce an `(r, s)`-tensor. Linear in the vector. -/
noncomputable def model_contract_covariant_bilinear (r s : ℕ) :
    E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E)
      (Tensor0SModel (s + 1) 𝕜 E)
      (Tensor0SModel s 𝕜 E)).comp
    (model_interior_bilinear 𝕜 E s)

set_option linter.unusedSectionVars false in
theorem model_contract_covariant_bilinear_apply (r s : ℕ) (v : E)
    (T : TensorRSModel r (s + 1) 𝕜 E) :
    model_contract_covariant_bilinear (𝕜 := 𝕜) (E := E) r s v T =
      (model_interior_product s v).comp T := rfl

/-- Model-level bilinear contraction contravariant-first: pairs a `(0,1)`-tensor (covector)
with a `(1+r, s)`-tensor to produce an `(r, s)`-tensor. Linear in the covector. -/
noncomputable def model_contract_contravariant_first_bilinear (r s : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (TensorRSModel (1 + r) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E) (Tensor0SModel (1 + r) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
    (model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r)

set_option linter.unusedSectionVars false in
theorem model_contract_contravariant_first_bilinear_apply (r s : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (T : TensorRSModel (1 + r) s 𝕜 E) :
    model_contract_contravariant_first_bilinear (𝕜 := 𝕜) (E := E) r s α T =
      T.comp (model_tensorWithCovector_first r α) := rfl

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
/-- Pointwise contraction of a (0,s+1)-tensor field with a vector field,
giving a (0,s)-tensor field. At each point `x`, this feeds `X(x)` into the first
slot of the (0,s+1)-tensor `α(x)` via the currying isomorphism. -/
noncomputable def contract_Tensor0SField_fun (s : ℕ)
    (α : (x : M) → Tensor0SSpace (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → Tensor0SSpace s I x :=
  fun x => interior_product s x (X x) (α x)

/-- Contraction of a smooth (0,s+1)-tensor field with a smooth vector field
yields a smooth (0,s)-tensor field.

If `α` is a smooth section of `T⁰_{s+1}M` and `X` is a smooth section of `TM`,
then the interior product `ι_X α`, defined pointwise by `(ι_X α)_x = ι_{X(x)} α_x`,
is a smooth section of `T⁰_s M`.

The proof reduces to smoothness of the bilinear model-level operation
`model_interior_bilinear` applied to the trivialized vector field and the
trivialized (0,s+1)-tensor field. The trivialization compatibility is a `rfl`-style
unfolding once the trivialization map's evaluation is expanded. -/
noncomputable def contract_Tensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  refine ⟨contract_Tensor0SField_fun s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  -- The trivialized image of `(ι_X α)(x)` equals `model_interior_bilinear 𝕜 E s g̃(x) f̃(x)`
  -- on the trivialization base set, where `f̃` and `g̃` are trivialized α and X.
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x => model_interior_bilinear 𝕜 E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
            (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := model_interior_bilinear 𝕜 E s)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  -- Equality of two model-fiber elements, prove via funext on `Fin s → E`.
  ext v
  -- LHS unfolds to `(α x) (Fin.cons (X x) (symmL ∘ v))`
  -- RHS unfolds to `(α x) (symmL ∘ Fin.cons g̃(x) v)`
  -- These are equal because `symmL (g̃(x)) = X x` for `x` in the base set, and
  -- `Fin.cons` commutes with composition.
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) (X x : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · -- i = 0
    change (X x : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · -- i = j.succ
    intro j
    rfl

/-- Contraction of (r,s+1) tensor with a tangent vector to get (r,s).

Given `T : (0,r) →L (0,s+1)` and `v ∈ TangentSpace`, we post-compose `T` with
`interior_product v`. The composition is done on the model fiber side (where `compL`
is available on normed spaces) and transported back via `tensorRSSpace_continuousLinearEquiv`. -/
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (model_interior_product s (v : E))).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) r (s + 1) x).toContinuousLinearMap)

/-- Contraction of (r+1,s) tensor with a cotangent vector (1-form) to get (r,s).

Given `T : (0,r+1) →L (0,s)` and `α ∈ (0,1)`, we pre-compose `T` with the embedding
`β ↦ β ⊗ α : (0,r) →L (0,r+1)`. The composition is done on the model fiber side
(using `compL.flip` for pre-composition) and transported back via
`tensorRSSpace_continuousLinearEquiv`. -/
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  let α_model : Tensor0SModel 1 𝕜 E := Tensor0SSpace.toModel α
  let embed_model : Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
    model_tensorWithCovector r α_model
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (r + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)).flip embed_model).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) (r + 1) s x).toContinuousLinearMap)

/-!
## Trace contraction of (r+1, s+1) tensors

The standard tensor trace: contract one upper index with one lower index of a
(r+1, s+1)-tensor to produce an (r, s)-tensor. We pick the first slot on each side
(the trace over the leading upper/lower pair); slot-permuted variants are obtained
by pre/post-composing with `domDomCongr`.

Coordinate-free description: choose a basis `{e_k}` of the tangent space with dual
basis `{e^k}`. For `T : (0,r+1) →L (0,s+1)`, the trace acts on `β : (0,r)` and
`(w_1, …, w_s)` by
  `(tr T)(β)(w_1, …, w_s) = Σ_k T(β ⊗ e^k)(e_k, w_1, …, w_s)`.
This is independent of the basis (it is the categorical trace of the slot-isomorphism
`E ⊗ E^* ≅ End(E)` applied to the chosen pair of slots).
-/

/-- Convert a continuous linear covector into the corresponding one-slot covariant
model tensor. -/
noncomputable def model_covectorOfCLM :
    (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel 1 𝕜 E :=
  (continuousMultilinearCurryFin1 𝕜 E 𝕜).symm.toContinuousLinearMap

set_option linter.unusedSectionVars false in
@[simp]
theorem model_covectorOfCLM_apply (α : E →L[𝕜] 𝕜) (v : Fin 1 → E) :
    model_covectorOfCLM (𝕜 := 𝕜) (E := E) α v = α (v 0) := by
  change ((continuousMultilinearCurryFin1 𝕜 E 𝕜).symm α) v = α (v 0)
  rfl

/-- Model-level trace contraction of a `(1+r, s+1)` tensor to an `(r, s)` tensor.

Internally this uses the canonical finite basis of the model space. The public
pointwise operation below transports this model map through the bundle-fiber
equivalences, so the external API remains coordinate-free. -/
noncomputable def model_contract_trace (r s : ℕ) :
    TensorRSModel (1 + r) (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E :=
  let d := Module.finrank 𝕜 E
  let B : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) := B.cDualBasis
  ∑ i : Fin d,
    (model_contract_covariant_bilinear (𝕜 := 𝕜) (E := E) r s (B i)).comp
      (model_contract_contravariant_first_bilinear
        (𝕜 := 𝕜) (E := E) r (s + 1)
        (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (b i)))

set_option linter.unusedSectionVars false in
theorem model_contract_trace_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    model_contract_trace (𝕜 := 𝕜) (E := E) r s T =
      ∑ i : Fin (Module.finrank 𝕜 E),
        (model_contract_covariant_bilinear
          (𝕜 := 𝕜) (E := E) r s
          ((Module.finBasis 𝕜 E) i))
          ((model_contract_contravariant_first_bilinear
            (𝕜 := 𝕜) (E := E) r (s + 1)
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              ((Module.finBasis 𝕜 E).cDualBasis i))) T) := by
  simp [model_contract_trace]

/-- Pointwise trace contraction of a `(1+r, s+1)` tensor at `x` to an `(r, s)` tensor,
contracting the first upper slot with the first lower slot.

This is implemented by the finite-basis model trace and transported through the
fiber/model continuous linear equivalences. -/
noncomputable def contract_trace (r s : ℕ) (x : M) :
    TensorRSSpace (1 + r) (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((model_contract_trace (𝕜 := 𝕜) (E := E) r s).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
theorem contract_trace_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T =
      (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm
        (model_contract_trace (𝕜 := 𝕜) (E := E) r s
          (tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x T)) := by
  rfl

set_option linter.unusedSectionVars false in
private theorem trace_bilinear_change_frame_coord
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F ((LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i))
          ((Module.finBasis 𝕜 E) i) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
      (K (b i))) =
    ∑ i : Fin d, F (LinearMap.toContinuousLinearMap (b.coord i)) (b i)
  have h_cov : ∀ j : Fin d,
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) z
          = ∑ i : Fin d, b.coord j (K (b i)) * b.coord i (L z) := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin d, b.coord i (L z) • K (b i)) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j (K (∑ i : Fin d, b.coord i (L z) • b i)) := by
              congr 1
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
      _ = b.coord j (K (L z)) := by
              rw [show (∑ i : Fin d, b.coord i (L z) • b i) = L z from b.sum_repr (L z)]
      _ = b.coord j z := by rw [hKL z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i)))
        = ∑ i : Fin d, ∑ j : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i))
                = F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
                    (∑ j : Fin d, b.coord j (K (b i)) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (K (b i)) • b j) = K (b i) from
                    b.sum_repr (K (b i))]
            _ = ∑ j : Fin d, (b.coord j (K (b i))) •
                    F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Fin d, (b.coord j (K (b i))) •
              ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

set_option linter.unusedSectionVars false in
private theorem trace_bilinear_change_frame_cdual
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
  simpa [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]
    using trace_bilinear_change_frame_coord (𝕜 := 𝕜) (E := E) L K hKL F

private noncomputable def model_trace_pairing_first (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  let covToTensor : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
    ((ContinuousLinearMap.apply 𝕜 (Tensor0SModel (1 + r) 𝕜 E) β).comp
      ((model_tensorWithCovector_first_bilinear (𝕜 := 𝕜) (E := E) r).comp
        (model_covectorOfCLM (𝕜 := 𝕜) (E := E))))
  let covToOutput : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (s + 1) 𝕜 E :=
    T.comp covToTensor
  let evalTail : Tensor0SModel s 𝕜 E →L[𝕜] 𝕜 :=
    ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin s => E) 𝕜 tail
  let curry :
      Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] Tensor0SModel s 𝕜 E :=
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  let outputToPair : Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.compL 𝕜 E (Tensor0SModel s 𝕜 E) 𝕜) evalTail).comp curry
  outputToPair.comp covToOutput

set_option linter.unusedSectionVars false in
private theorem model_trace_pairing_first_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E)
    (α : E →L[𝕜] 𝕜) (X : E) :
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail α X =
      (model_interior_product s X
        (T (model_tensorWithCovector_first r
          (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β))) tail := by
  simp [model_trace_pairing_first, model_tensorWithCovector_first_bilinear_apply,
    model_interior_product]

set_option linter.unusedSectionVars false in
private theorem trace_bilinear_basis_coord
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Idx,
        F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
      ∑ j : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
          ((Module.finBasis 𝕜 E) j) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Idx,
      F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
    ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j)
  have h_cov : ∀ j : Fin d,
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) z
          = ∑ i : Idx, b.coord j (basis i) * basis.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Idx, basis.coord i z • basis i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Idx, basis.coord i z • basis i) = z from basis.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Idx, F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i))
        = ∑ i : Idx, ∑ j : Fin d,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)
                = F (LinearMap.toContinuousLinearMap (basis.coord i))
                    (∑ j : Fin d, b.coord j (basis i) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (basis i) • b j) = basis i from
                    b.sum_repr (basis i)]
            _ = ∑ j : Fin d, (b.coord j (basis i)) •
                    F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Idx,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Idx, (b.coord j (basis i)) •
              LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

set_option linter.unusedSectionVars false in
/-- Model trace contraction evaluated in an arbitrary finite basis. -/
theorem model_contract_trace_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E) (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (model_contract_trace (𝕜 := 𝕜) (E := E) r s T β) tail =
      ∑ i : Idx,
        (model_interior_product s (basis i)
          (T (model_tensorWithCovector_first r
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail := by
  rw [model_contract_trace_apply]
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousMultilinearMap.sum_apply]
  symm
  calc
    (∑ i : Idx,
        (model_interior_product s (basis i)
          (T (model_tensorWithCovector_first r
            (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail)
        = ∑ i : Idx,
            model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
              (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply]
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
            (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
            ((Module.finBasis 𝕜 E) j) := by
          exact trace_bilinear_basis_coord (𝕜 := 𝕜) (E := E) basis
            (model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail)
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          (model_contract_covariant_bilinear
            (𝕜 := 𝕜) (E := E) r s
            ((Module.finBasis 𝕜 E) j))
            ((model_contract_contravariant_first_bilinear
              (𝕜 := 𝕜) (E := E) r (s + 1)
              (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
                ((Module.finBasis 𝕜 E).cDualBasis j))) T) β tail := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [model_trace_pairing_first_apply,
            model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          simp [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]

/-- Precompose every covariant slot of a model `(0,k)` tensor by `L`. -/
noncomputable def model_covariantChange (k : ℕ) (L : E →L[𝕜] E) :
    Tensor0SModel k 𝕜 E →L[𝕜] Tensor0SModel k 𝕜 E :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)

set_option linter.unusedSectionVars false in
@[simp]
theorem model_covariantChange_apply (k : ℕ) (L : E →L[𝕜] E)
    (T : Tensor0SModel k 𝕜 E) (v : Fin k → E) :
    model_covariantChange (𝕜 := 𝕜) (E := E) k L T v =
      T (fun i => L (v i)) := by
  rfl

set_option linter.unusedSectionVars false in
private theorem model_interior_product_covariantChange_apply (s : ℕ)
    (L : E →L[𝕜] E) (X : E) (U : Tensor0SModel (s + 1) 𝕜 E)
    (v : Fin s → E) :
    (model_interior_product s X
      (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)) v =
    (model_interior_product s (L X) U) (fun i => L (v i)) := by
  change (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)
      (Fin.cons X v) =
    U (Fin.cons (L X) (fun i => L (v i)))
  rw [model_covariantChange_apply]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

set_option linter.unusedSectionVars false in
private theorem model_covariantChange_tensorWithCovector_first (r : ℕ)
    (L : E →L[𝕜] E) (α : E →L[𝕜] 𝕜) (β : Tensor0SModel r 𝕜 E) :
    model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) L
      (model_tensorWithCovector_first r (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β) =
    model_tensorWithCovector_first r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (model_covariantChange (𝕜 := 𝕜) (E := E) r L β) := by
  refine ContinuousMultilinearMap.ext fun w => ?_
  change (Bundle.continuousMultilinearMap.modelProduct 1 r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) α) β)
      (fun i => L (w i)) =
    (Bundle.continuousMultilinearMap.modelProduct 1 r
      (model_covectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (model_covariantChange (𝕜 := 𝕜) (E := E) r L β)) w
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- Model trace commutes with an invertible change of frame.

This is the reusable algebraic content behind smoothness of trace contraction on
the tensor bundle: the trace finite sum is independent of the local frame used
to trivialize the tangent bundle. -/
theorem model_contract_trace_naturality
    (r s : ℕ) (L Linv : E →L[𝕜] E)
    (hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E)
    (_hR : Linv.comp L = ContinuousLinearMap.id 𝕜 E)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    model_contract_trace (𝕜 := 𝕜) (E := E) r s
      ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (T.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv))) =
    (model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
      ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T).comp
        (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
  ext β v
  let β' : Tensor0SModel r 𝕜 E :=
    model_covariantChange (𝕜 := 𝕜) (E := E) r Linv β
  let tail : Fin s → E := fun i => L (v i)
  let F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β' tail
  have hKL : ∀ z : E, L (Linv z) = z := by
    intro z
    have h := congrArg (fun f : E →L[𝕜] E => f z) hL
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    ((model_contract_trace (𝕜 := 𝕜) (E := E) r s
        ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
          (T.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)))) β) v
        =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
          (L ((Module.finBasis 𝕜 E) i)) := by
          rw [model_contract_trace_apply]
          rw [ContinuousLinearMap.sum_apply]
          rw [ContinuousMultilinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          change (model_interior_product s ((Module.finBasis 𝕜 E) i)
              ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
                (T ((model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)
                  (model_tensorWithCovector_first r
                    (model_covectorOfCLM (𝕜 := 𝕜) (E := E)
                      ((Module.finBasis 𝕜 E).cDualBasis i)) β))))) v =
            F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
              (L ((Module.finBasis 𝕜 E) i))
          rw [model_interior_product_covariantChange_apply]
          rw [model_covariantChange_tensorWithCovector_first]
          rw [model_trace_pairing_first_apply]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
          exact trace_bilinear_change_frame_cdual (𝕜 := 𝕜) (E := E)
            (L := Linv) (K := L) hKL F
    _ =
      (((model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T).comp
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv))) β) v := by
          change ∑ i : Fin (Module.finrank 𝕜 E),
              F ((Module.finBasis 𝕜 E).cDualBasis i)
                ((Module.finBasis 𝕜 E) i) =
            (model_covariantChange (𝕜 := 𝕜) (E := E) s L
              ((model_contract_trace (𝕜 := 𝕜) (E := E) r s T) β')) v
          rw [model_covariantChange_apply]
          rw [model_contract_trace_apply]
          rw [ContinuousLinearMap.sum_apply]
          rw [ContinuousMultilinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply,
            model_contract_covariant_bilinear_apply,
            model_contract_contravariant_first_bilinear_apply]
          rfl

set_option linter.unusedSectionVars false in
/-- Naturality of trace contraction under the local trivialization at `x₀`.

This is the compatibility used by `contract_TensorRSField`: trivializing after
pointwise trace is the same as applying the model trace after trivializing the
original tensor. -/
theorem contract_trace_trivialization_eq
    {r s : ℕ} {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    (trivializationAt (TensorRSModel r s 𝕜 E)
      (fun y => TensorRSSpace r s I y) x₀
      ⟨x, contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
    model_contract_trace (𝕜 := 𝕜) (E := E) r s
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (fun y => TensorRSSpace (1 + r) (s + 1) I y) x₀
        ⟨x, T⟩).2) := by
  let L : E →L[𝕜] E := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
  let Linv : E →L[𝕜] E :=
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
  let Tx : TensorRSModel (1 + r) (s + 1) 𝕜 E :=
    tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x T
  have hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx z
  have hR : Linv.comp L = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL
      (R := 𝕜) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt 𝕜 x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel k 𝕜 E)
          (fun y => Tensor0SSpace k I y) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SModel k 𝕜 E) (u : Fin k → E),
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[𝕜] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i
      exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x U) u
          = ((trivializationAt (Tensor0SModel k 𝕜 E)
              (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SModel k 𝕜 E)
            (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel k 𝕜 E)
              (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SModel k 𝕜 E)
              (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt_symmL
              (R := 𝕜) hx]
  have h_input :
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (fun y => TensorRSSpace (1 + r) (s + 1) I y) x₀
        ⟨x, T⟩).2) =
      (model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (Tx.comp (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun y => Tensor0SSpace (s + 1) I y) x₀).continuousLinearMapAt 𝕜 x
        (T ((trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (fun y => Tensor0SSpace (1 + r) I y) x₀).symmL 𝕜 x β)) v =
      ((model_covariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
        (Tx ((model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (fun y => Tensor0SSpace (1 + r) I y) x₀).symmL 𝕜 x β =
          (model_covariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]
      rfl
    rw [hβ]
    rfl
  have h_output :
      (trivializationAt (TensorRSModel r s 𝕜 E)
        (fun y => TensorRSSpace r s I y) x₀
        ⟨x, contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
      (model_covariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s Tx).comp
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun y => Tensor0SSpace s I y) x₀).continuousLinearMapAt 𝕜 x
        ((contract_trace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T)
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (fun y => Tensor0SSpace r I y) x₀).symmL 𝕜 x β)) v =
      ((model_covariantChange (𝕜 := 𝕜) (E := E) s L)
        ((model_contract_trace (𝕜 := 𝕜) (E := E) r s Tx)
          ((model_covariantChange (𝕜 := 𝕜) (E := E) r Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    rw [contract_trace_apply]
    have hβ :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun y => Tensor0SSpace r I y) x₀).symmL 𝕜 x β =
          (model_covariantChange (𝕜 := 𝕜) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]
      rfl
    rw [hβ]
    rfl
  rw [h_input, h_output]
  exact (model_contract_trace_naturality (𝕜 := 𝕜) (E := E)
    r s L Linv hL hR Tx).symm

/-!
## Field-level contractions

Lifts of the pointwise contraction operations to smooth tensor fields:

* `contract_covariantField r s α X`: post-compose with the interior product of `X`
  pointwise. Smoothness reduces to smoothness of `model_interior_bilinear` applied
  to the trivialized vector field and trivialized (r, s+1)-tensor field, using the
  same `congr_of_eventuallyEq` pattern as `contract_Tensor0SField`.
* `contract_contravariantField r s α ω`: pre-compose with `β ↦ β ⊗ ω(x)` pointwise.
  Smoothness uses bilinearity of `modelProduct` together with smoothness of `α` and `ω`.
* `contract_TensorRSField r s T`: pointwise trace, smoothness via the basis-coord
  criterion (since the trace is a finite sum of basis-coord values).
-/

/-- Pointwise contraction of an (r, s+1)-tensor field with a vector field. -/
noncomputable def contract_covariantField_fun (r s : ℕ)
    (α : (x : M) → TensorRSSpace r (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_covariant r s x (X x) (α x)

set_option maxHeartbeats 400000 in
-- The `change` reductions through the hom-bundle trivialization and id-equiv currying
-- are heavy; we raise the heartbeat limit accordingly.
/-- Contraction of a smooth (r, s+1)-tensor field with a smooth vector field, yielding
a smooth (r, s)-tensor field.

The proof structure mirrors `contract_Tensor0SField`: trivializing the contracted field
gives `biop X̃(x) α̃(x)` where `biop = compL ∘ model_interior_bilinear`, which is smooth
as a clm-application of two smooth trivialized sections. The trivialization compatibility
is reduced via `Trivialization.continuousLinearMapAt_apply` and `coe_linearMapAt_of_mem`
on the (0,s) and (0,s+1) bundles, both wrapped inside the (r, s)/(r, s+1) hom bundles. -/
noncomputable def contract_covariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r (s + 1)
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨contract_covariantField_fun r s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  -- Bilinear model operation: `biop X̃ T̃ = (mip X̃).comp T̃` post-composes a (r, s+1)
  -- model section with the model interior product against `X̃ : E`.
  set biop :
      E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (s + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).comp
      (model_interior_bilinear 𝕜 E s) with hbiop
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (TensorRSModel r (s + 1) 𝕜 E)
            (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsL
  set Xtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hXtilde
  set gtilde : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x γ
    with hgtilde
  -- Helper rewrites: on the trivialization base set, the (0, k) bundle's
  -- `continuousLinearMapAt` evaluates to `T (fun i => sL (v i))`.
  have h_cLMAt_s : ∀ (T : Tensor0SSpace s I x) (v : Fin s → E),
      (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_s1 : ∀ (T : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1) → E),
      (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
          (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  -- Both sides of the goal reduce by definitional unfolding of the hom-bundle
  -- trivialization (`continuousLinearMap_apply`) and the pointwise reductions
  -- `contract_covariant ... = mip ∘ ...` and `biop = compL ∘ mib`.
  change (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      (model_interior_product s (X x : E) ((α x) gtilde)) w =
    (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
      (fun x => Tensor0SSpace (s + 1) I x) x₀).continuousLinearMapAt 𝕜 x ((α x) gtilde)
      (Fin.cons Xtilde w)
  rw [h_cLMAt_s, h_cLMAt_s1]
  -- After unfolding, both sides apply `(α x) gtilde` to a `Fin (s+1) → E` vector.
  -- LHS uses `Fin.cons (X x) (sL ∘ w)`, RHS uses `sL ∘ Fin.cons Xtilde w`.
  change ((α x) gtilde : Tensor0SModel (s + 1) 𝕜 E)
      (@Fin.cons s (fun _ => E) (X x : E) (fun i => sL (w i))) =
    ((α x) gtilde) (fun i => sL (@Fin.cons s (fun _ => E) Xtilde w i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · -- i = 0: `X x = sL Xtilde` since `Xtilde = cLMAt (X x)` and `sL ∘ cLMAt = id`.
    change (X x : E) = sL Xtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x)
        = Xtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · -- i = j.succ: both sides reduce to `sL (w j)`.
    intro j
    rfl

/-- Pointwise contraction of an (r+1, s)-tensor field with a 1-form field. -/
noncomputable def contract_contravariantField_fun (r s : ℕ)
    (α : (x : M) → TensorRSSpace (r + 1) s I x)
    (φ : (x : M) → Tensor0SSpace 1 I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_contravariant r s x (φ x) (α x)

set_option maxHeartbeats 800000 in
-- The `change` reductions through the hom-bundle trivialization and the covector
-- tensor-product embedding are heavy; we raise the heartbeat limit accordingly.
/-- Contraction of a smooth (r+1, s)-tensor field with a smooth 1-form field, yielding
a smooth (r, s)-tensor field.

The proof structure mirrors `contract_covariantField`: trivializing the contracted field
gives `biop_ctr φ̃(x) α̃(x)` where `biop_ctr α̃ T̃ = T̃.comp (model_tensorWithCovector r α̃)`,
built as a CLM-bilinear via `compL.flip` and a `mtwc_bilinear` packaging of
`model_tensorWithCovector` in its covector argument. Smoothness follows as a
clm-application of two smooth trivialized sections. The pointwise equality reduces via
the hom-bundle `continuousLinearMap_apply` together with `continuousLinearMapAt_apply`
and `coe_linearMapAt_of_mem` on the (0,r), (0,r+1), (0,s), and (0,1) bundles, plus the
cancellation `symmL_continuousLinearMapAt` for the tangent trivialization. -/
noncomputable def contract_contravariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (r + 1) s)
    (φ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 1) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (r + 1) s
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1
  refine ⟨contract_contravariantField_fun r s (fun x => α x) (fun x => φ x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hφ := φ.contMDiff x₀
  rw [contMDiffAt_section] at hφ
  -- Bilinear packaging of `model_tensorWithCovector` in its covector argument. The
  -- resulting linear map of `α̃` is continuous because `Tensor0SModel 1 𝕜 E` is
  -- finite-dimensional.
  let mtwc_bilinear :
      Tensor0SModel 1 𝕜 E →L[𝕜] (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => model_tensorWithCovector r a
        map_add' := fun a₁ a₂ => by
          refine ContinuousLinearMap.ext fun β => ?_
          refine ContinuousMultilinearMap.ext fun w => ?_
          simp only [model_tensorWithCovector, LinearMap.coe_toContinuousLinearMap',
            LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.add_apply,
            Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.add_apply, mul_add]
        map_smul' := fun c a => by
          refine ContinuousLinearMap.ext fun β => ?_
          refine ContinuousMultilinearMap.ext fun w => ?_
          simp only [model_tensorWithCovector, LinearMap.coe_toContinuousLinearMap',
            LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smul_apply,
            Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
  -- The bilinear model operation `biop_ctr α̃ T̃ = T̃.comp (model_tensorWithCovector r α̃)`
  -- pre-composes the trivialized (r+1, s)-tensor `T̃` with the tensor-with-covector
  -- embedding, yielding a trivialized (r, s)-tensor.
  set biop_ctr :
      Tensor0SModel 1 𝕜 E →L[𝕜] (TensorRSModel (r + 1) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (r + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
      mtwc_bilinear with hbiop
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop_ctr
          ((trivializationAt (Tensor0SModel 1 𝕜 E)
            (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2)
          ((trivializationAt (TensorRSModel (r + 1) s 𝕜 E)
            (fun x => TensorRSSpace (r + 1) s I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop_ctr)).clm_apply hφ).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun β => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsL
  -- Helper rewrites: on the trivialization base set, the (0, k) bundle's
  -- `continuousLinearMapAt` evaluates to `T (fun i => sL (v i))`.
  have h_cLMAt_s : ∀ (T : Tensor0SSpace s I x) (u : Fin s → E),
      (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_r : ∀ (T : Tensor0SSpace r I x) (u : Fin r → E),
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_r1 : ∀ (T : Tensor0SSpace (r + 1) I x) (u : Fin (r + 1) → E),
      (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
        (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
        (fun x => Tensor0SSpace (r + 1) I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_1 : ∀ (T : Tensor0SSpace 1 I x) (u : Fin 1 → E),
      (trivializationAt (Tensor0SModel 1 𝕜 E)
        (fun x => Tensor0SSpace 1 I x) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => sL (u i)) := by
    intro T u
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel 1 𝕜 E)
        (fun x => Tensor0SSpace 1 I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel 1 𝕜 E)
          (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  -- Abbreviations for the two bundle-fiber elements we need to compare inside `(α x)`.
  set β_symm : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β
    with hβ_symm
  set atilde_x : Tensor0SModel 1 𝕜 E :=
    (trivializationAt (Tensor0SModel 1 𝕜 E) (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2
    with hatilde_x
  -- Unfold the hom-bundle trivialization on both sides. LHS: `contract_contravariant` reduces
  -- via the id-as-CLE `tRSeq` to `(α x) (mtwc r (toModel (φ x)) β_symm)`. RHS: `biop_ctr` unfolds
  -- to `T̃.comp (mtwc r atilde_x) β = T̃ (mtwc r atilde_x β)`, and `T̃` further unfolds to
  -- `cLMAt_s ∘ (α x) ∘ symmL_{r+1}`.
  change (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      ((α x) (model_tensorWithCovector r (Tensor0SSpace.toModel (φ x)) β_symm)) v =
    (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x
      ((α x) ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
        (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
        (model_tensorWithCovector r atilde_x β))) v
  rw [h_cLMAt_s, h_cLMAt_s]
  -- Both sides are now `(α x) Y_i (fun i => sL (v i))` for some `Y_i : Tensor0SSpace (r+1) I x`.
  -- Reduce to `Y_1 = Y_2` at the `(r+1)` level (peel off the `v`-application then the `α x`).
  congr 1
  congr 1
  -- LHS: `mtwc r (toModel (φ x)) β_symm`; RHS: `symmL_{r+1} (mtwc r atilde_x β)`.
  -- `ContinuousMultilinearMap.ext` at `Fin (r+1) → TangentSpace I x` level, then cancel
  -- `symmL ∘ cLMAt = id` on the RHS to reduce to a pure `modelProduct` equality.
  refine ContinuousMultilinearMap.ext fun w => ?_
  have hw : w = fun i => sL ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
      𝕜 x (w i)) := by
    funext i
    exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (w i)).symm
  -- Compute the RHS explicitly via a calc chain (bypasses higher-order `rw` matching).
  have hrhs :
      ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
          ((model_tensorWithCovector r atilde_x) β)) w =
        ((model_tensorWithCovector r atilde_x) β)
          (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) := by
    calc ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
            ((model_tensorWithCovector r atilde_x) β)) w
        = ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
              (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
              ((model_tensorWithCovector r atilde_x) β))
            (fun i => sL ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
              𝕜 x (w i))) := by rw [← hw]
      _ = (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
              (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
              ((model_tensorWithCovector r atilde_x) β))
            (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) :=
          (h_cLMAt_r1 _ _).symm
      _ = ((model_tensorWithCovector r atilde_x) β)
            (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i)) := by
          rw [(trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).continuousLinearMapAt_symmL (R := 𝕜) hx]
  refine Eq.trans ?_ hrhs.symm
  -- Now both sides are `modelProduct`-style expressions. Unfold via `modelProduct_apply`.
  change (Bundle.continuousMultilinearMap.modelProduct r 1 β_symm
      (Tensor0SSpace.toModel (φ x))) w =
    Bundle.continuousMultilinearMap.modelProduct r 1 β atilde_x
      (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (w i))
  rw [Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  -- Two factors to match. First factor: `β_symm (w ∘ castAdd 1) = β (fun i => cL (w ∘ castAdd 1 i))`.
  -- Second factor: `toModel (φ x) (w ∘ natAdd r) = atilde_x (fun i => cL (w ∘ natAdd r i))`.
  congr 1
  · -- first factor: `β_symm (w ∘ castAdd 1) = β (fun i => cL (w ∘ castAdd 1 i))`
    -- Both unfold via the same cancellation (β_symm = symmL β, cLMAt ∘ symmL = id).
    have hwc : (w ∘ Fin.castAdd 1) = fun i => sL
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          ((w ∘ Fin.castAdd 1) i)) := by
      funext i
      exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx ((w ∘ Fin.castAdd 1) i)).symm
    conv_lhs => rw [hwc]
    rw [← h_cLMAt_r]
    rw [(trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt_symmL (R := 𝕜) hx]
    rfl
  · -- second factor: `toModel (φ x) (w ∘ natAdd r) = atilde_x (fun i => cL (w ∘ natAdd r i))`
    -- `atilde_x u' = toModel (φ x) (fun i => sL (u' i))` since `atilde_x = cLMAt_{0,1} (toModel (φ x))`
    -- on baseSet; apply `h_cLMAt_1` to the RHS via this identification.
    have h_atilde_eq :
        (trivializationAt (Tensor0SModel 1 𝕜 E) (fun x => Tensor0SSpace 1 I x) x₀).continuousLinearMapAt
          𝕜 x (Tensor0SSpace.toModel (φ x)) = atilde_x := by
      ext u'
      rw [h_cLMAt_1]
      rfl
    have hwn : (w ∘ Fin.natAdd r) = fun i => sL
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
          ((w ∘ Fin.natAdd r) i)) := by
      funext i
      exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx ((w ∘ Fin.natAdd r) i)).symm
    conv_lhs => rw [hwn]
    rw [← h_cLMAt_1]
    rw [h_atilde_eq]
    rfl

/-- Pointwise trace contraction of a `(1+r, s+1)` tensor field. -/
noncomputable def contract_TensorRSField_fun (r s : ℕ)
    (T : (x : M) → TensorRSSpace (1 + r) (s + 1) I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contract_trace r s x (T x)

/-- Trace contraction of a smooth `(1+r, s+1)` tensor field, yielding a smooth
`(r, s)` tensor field.

The field-level proof is deliberately only the smooth-section skeleton: after
trivializing the input field, compose with the constant model trace and use
`contract_trace_trivialization_eq` for the pointwise frame-compatibility. -/
noncomputable def contract_TensorRSField (r s : ℕ)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
      (1 + r) (s + 1)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨contract_TensorRSField_fun r s (fun x => T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hTrace :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => model_contract_trace (𝕜 := 𝕜) (E := E) r s
          ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
            (fun x => TensorRSSpace (1 + r) (s + 1) I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    (model_contract_trace (𝕜 := 𝕜) (E := E) r s).contMDiffAt.comp x₀ hT
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  exact contract_trace_trivialization_eq
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) (x₀ := x₀) (x := x) hx (T x)

end FieldContraction

end
end Tensor0SBundle
