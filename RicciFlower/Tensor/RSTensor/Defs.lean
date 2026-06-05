/-
Authors: Yuan Liao, Jack McCarthy
-/
import RicciFlower.Tensor.Multilinear.Fiber
import RicciFlower.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Tensor Definitions and Bundle Instances

We define the model fibers and point-wise fibers for covariant and mixed tensor bundles
on smooth manifolds. The (0,s) covariant tensor bundle is defined as a
`Bundle.continuousMultilinearMap` applied to the tangent bundle, inheriting its smooth
vector bundle structure. The (r,s) tensor bundle is defined using
`Bundle.ContinuousLinearMap` between (0,r)- and (0,s)-tensor bundles.

## Main Definitions

* `Tensor0SModel s 𝕜 E` : the model fiber for the (0,s) covariant tensor bundle;
  continuous multilinear maps from `s` copies of `E` to `𝕜`.
* `TensorRSModel r s 𝕜 E` : the model fiber for the (r,s) tensor bundle;
  continuous linear maps from `Tensor0SModel r` to `Tensor0SModel s`.
* `Tensor0SSpace s I x` : the fiber of the (0,s) covariant tensor bundle at `x ∈ M`;
  defined as `Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`.
* `CotangentSpace I x` : the cotangent space at `x`, i.e. `Tensor0SSpace 1 I x`.
* `TensorRSSpace r s I x` : the fiber of the (r,s) tensor bundle at `x`;
  continuous linear maps from (0,r)-tensors to (0,s)-tensors.
* `tensor0S_curry s x` : the currying equivalence
  `Tensor0SSpace (s+1) I x ≃L[𝕜] (TangentSpace I x →L[𝕜] Tensor0SSpace s I x)`.

## Bundle Instances

* `tensor0SBundle_fiber s` : the (0,s)-tensor bundle is a fiber bundle.
* `tensor0SBundle_vector s` : the (0,s)-tensor bundle is a vector bundle.
* `tensor0SBundle_smooth s` : the (0,s)-tensor bundle is a smooth vector bundle.
* `tensorRSBundle_topology r s` : topology on the (r,s)-tensor bundle total space.
* `tensorRSBundle_fiber r s` : the (r,s)-tensor bundle is a fiber bundle.
* `tensorRSBundle_vector r s` : the (r,s)-tensor bundle is a vector bundle.
* `tensorRSBundle_smooth r s` : the (r,s)-tensor bundle is a smooth vector bundle.

## Tags

tensor, covariant tensor, smooth manifold, differential geometry, vector bundle
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x' : M}
variable {r s : ℕ}

/-!
## Model Fibers
-/

/-- The trivial line bundle over `M` with constant fiber `𝕜`. -/
abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

/-- The model fiber for the bundle of (0,s) covariant tensors:
continuous multilinear maps from `s` copies of `E` to `𝕜`. -/
@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

/-- The model fiber for the (r,s)-tensor bundle: continuous linear maps from (0,r)-tensors
to (0,s)-tensors, realizing `V* ⊗ W ≅ Hom(V, W)` for finite-dimensional `V`. -/
@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

namespace Tensor0SModel

/-- Evaluate a model `(0,0)` tensor at its unique empty slot. -/
noncomputable def eval0 :
    Tensor0SModel 0 𝕜 E →L[𝕜] 𝕜 :=
  (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem eval0_apply (T : Tensor0SModel 0 𝕜 E) :
    eval0 (𝕜 := 𝕜) (E := E) T = T Fin.elim0 := by
  change (continuousMultilinearCurryFin0 𝕜 E 𝕜) T = T Fin.elim0
  rw [continuousMultilinearCurryFin0_apply]
  exact congrArg T (Subsingleton.elim _ _)

/-- Embed a model covariant tensor as a mixed model tensor with zero upper slots. -/
noncomputable def toRS0 {s : ℕ}
    (T : Tensor0SModel s 𝕜 E) :
    TensorRSModel 0 s 𝕜 E :=
  (eval0 (𝕜 := 𝕜) (E := E)).smulRight T

/-- The zero-upper-slot embedding of covariant model tensors as a continuous
linear map. -/
noncomputable def toRS0L {s : ℕ} :
    Tensor0SModel s 𝕜 E →L[𝕜] TensorRSModel 0 s 𝕜 E :=
  ContinuousLinearMap.smulRightL 𝕜
    (Tensor0SModel 0 𝕜 E) (Tensor0SModel s 𝕜 E)
    (eval0 (𝕜 := 𝕜) (E := E))

@[simp]
theorem toRS0_apply {s : ℕ}
    (T : Tensor0SModel s 𝕜 E) (c : Tensor0SModel 0 𝕜 E) :
    toRS0 (𝕜 := 𝕜) (E := E) T c =
      c Fin.elim0 • T := by
  rw [toRS0, ContinuousLinearMap.smulRight_apply, eval0_apply]

@[simp] theorem toRS0L_apply {s : ℕ}
    (T : Tensor0SModel s 𝕜 E) :
    toRS0L (𝕜 := 𝕜) (E := E) T =
      toRS0 (𝕜 := 𝕜) (E := E) T := by
  rfl

/-- The unit model `(0,0)` tensor. -/
def one0 : Tensor0SModel 0 𝕜 E :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E) (1 : 𝕜)

@[simp]
theorem one0_apply (v : Fin 0 → E) :
    one0 (𝕜 := 𝕜) (E := E) v = (1 : 𝕜) := by
  rw [one0, ContinuousMultilinearMap.constOfIsEmpty_apply]

/-- A model `(0,0)` tensor is its scalar value times the unit `(0,0)` tensor. -/
theorem eq_smul_one0 (c : Tensor0SModel 0 𝕜 E) :
    c = c Fin.elim0 • one0 (𝕜 := 𝕜) (E := E) := by
  ext v
  change c v = c Fin.elim0 * (one0 (𝕜 := 𝕜) (E := E) v)
  rw [one0_apply, mul_one]
  exact congrArg c (Subsingleton.elim v Fin.elim0)

/-- Evaluate a zero-upper-slot mixed model tensor on the unit `(0,0)` tensor. -/
noncomputable def fromRS0L {s : ℕ} :
    TensorRSModel 0 s 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  ContinuousLinearMap.apply 𝕜 (Tensor0SModel s 𝕜 E)
    (one0 (𝕜 := 𝕜) (E := E))

@[simp]
theorem fromRS0L_apply {s : ℕ} (T : TensorRSModel 0 s 𝕜 E) :
    fromRS0L (𝕜 := 𝕜) (E := E) T =
      T (one0 (𝕜 := 𝕜) (E := E)) := by
  rfl

/-- The natural continuous linear equivalence
`Tensor0SModel s ≃L TensorRSModel 0 s`.

It sends a covariant tensor `T` to the mixed tensor `c ↦ c() • T`; the inverse
evaluates a zero-upper-slot mixed tensor on the unit `(0,0)` tensor. -/
noncomputable def rs0Equiv {s : ℕ} :
    Tensor0SModel s 𝕜 E ≃L[𝕜] TensorRSModel 0 s 𝕜 E where
  toFun := toRS0 (𝕜 := 𝕜) (E := E)
  invFun := fun T => T (one0 (𝕜 := 𝕜) (E := E))
  left_inv := by
    intro T
    change toRS0 (𝕜 := 𝕜) (E := E) T (one0 (𝕜 := 𝕜) (E := E)) = T
    rw [toRS0_apply, one0_apply, one_smul]
  right_inv := by
    intro T
    apply ContinuousLinearMap.ext
    intro c
    change toRS0 (𝕜 := 𝕜) (E := E)
        (T (one0 (𝕜 := 𝕜) (E := E))) c = T c
    rw [toRS0_apply]
    calc
      c Fin.elim0 • T (one0 (𝕜 := 𝕜) (E := E)) =
          T (c Fin.elim0 • one0 (𝕜 := 𝕜) (E := E)) := by
            exact (map_smul T (c Fin.elim0) (one0 (𝕜 := 𝕜) (E := E))).symm
      _ = T c := by
            rw [← eq_smul_one0 (𝕜 := 𝕜) (E := E) c]
  map_add' := by
    intro T U
    apply ContinuousLinearMap.ext
    intro c
    simp [toRS0_apply, smul_add]
  map_smul' := by
    intro a T
    apply ContinuousLinearMap.ext
    intro c
    simp [toRS0_apply, smul_smul, mul_comm]
  continuous_toFun := (toRS0L (𝕜 := 𝕜) (E := E)).continuous
  continuous_invFun := (fromRS0L (𝕜 := 𝕜) (E := E)).continuous

@[simp]
theorem rs0Equiv_apply {s : ℕ} (T : Tensor0SModel s 𝕜 E) :
    rs0Equiv (𝕜 := 𝕜) (E := E) T =
      toRS0 (𝕜 := 𝕜) (E := E) T := by
  rfl

@[simp]
theorem rs0Equiv_symm_apply {s : ℕ} (T : TensorRSModel 0 s 𝕜 E) :
    (rs0Equiv (𝕜 := 𝕜) (E := E) (s := s)).symm T =
      T (one0 (𝕜 := 𝕜) (E := E)) := by
  rfl

end Tensor0SModel

/-!
## Point-wise Fibers
-/

/-- The fiber of the (0,s) covariant tensor bundle at `x ∈ M`, defined as
`Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`. -/
abbrev Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x

/-- The cotangent space at `x ∈ M`: linear functionals on the tangent space,
realized as (0,1)-tensors. -/
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace 1 I x

/-- The fiber of the (r,s)-tensor bundle at `x ∈ M`: continuous linear maps from
(0,r)-tensors to (0,s)-tensors, using `(V⊗W)* ≅ V*⊗W*` and `V*⊗W ≅ Hom(V,W)`. -/
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

/-!
## Model Fiber Instances
-/

/-- `Tensor0SModel s 𝕜 E` is a normed additive commutative group. -/
instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

/-- `Tensor0SModel s 𝕜 E` is a normed `𝕜`-module. -/
instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hs : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hr : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  apply @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
     _ _ _ _ hr hs _ _

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) :=
  inferInstance

/-- `TensorRSModel r s 𝕜 E` is a normed `𝕜`-module. -/
instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

/-!
## Point-wise Fiber Instances

The bundle and norm topologies on `Tensor0SSpace s I x` agree because the trivialization at
each point gives a continuous linear equivalence to the model fiber, and all Hausdorff
locally convex topologies on a finite-dimensional space agree.
-/

/-- The tangent space at any point is a normed additive commutative group, inherited from `E`. -/
instance tangentSpace_normedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- The tangent space at any point is a normed `𝕜`-module, inherited from `E`. -/
instance tangentSpace_normedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (NormedSpace 𝕜 E)

instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional 𝕜 E)

instance tangentSpace_moduleFree (x : M) :
    Module.Free 𝕜 (TangentSpace I x) :=
  inferInstanceAs (Module.Free 𝕜 E)

omit [FiniteDimensional 𝕜 E] in
/-- Alias for the general `Bundle.continuousMultilinearMap.topology_eq`, specialized to the
tangent bundle. Used internally by `tensor0SSpace_continuousLinearEquiv`. -/
private theorem tensor0SSpace_topology_eq (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) :=
  Bundle.continuousMultilinearMap.topology_eq s x

noncomputable instance tensor0SSpace_finiteDimensional [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.instFiniteDimensional s x

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  Bundle.continuousMultilinearMap.finrank_eq s x

omit [FiniteDimensional 𝕜 E] in
/-- `Tensor0SSpace s I x` is definitionally equal to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`, since `TangentSpace I x = E`. -/
private theorem tensor0SSpace_type_eq (s : ℕ) (x : M) :
    Tensor0SSpace s I x =
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 := by
  unfold Tensor0SSpace Bundle.continuousMultilinearMap
  rfl

/-- The fiber `Tensor0SSpace s I x` is continuously linearly isomorphic to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`: the underlying types are definitionally
equal and the topologies agree by `tensor0SSpace_topology_eq`. -/
def tensor0SSpace_continuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Tensor0SSpace s I x) (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜) (Tensor0SSpace s I x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

/-!
## Coercion to Model Fiber

The continuous linear equivalence `tensor0SSpace_continuousLinearEquiv` identifies each fiber
`Tensor0SSpace s I x` with `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`.  We package
this as `Tensor0SSpace.toModel` (forward direction) and `Tensor0SSpace.ofModel`
(its inverse), together with linearity, continuity, and invertibility lemmas.
-/

namespace Tensor0SSpace

/-- Coerce a `Tensor0SSpace` fiber element to the model fiber.
This is the forward direction of `tensor0SSpace_continuousLinearEquiv`. -/
def toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  tensor0SSpace_continuousLinearEquiv s x T

/-- `Tensor0SSpace.toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (s : ℕ) (x : M) :
    Tensor0SSpace s I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  (tensor0SSpace_continuousLinearEquiv s x).toContinuousLinearMap

/-- Evaluate a `(0,0)` tensor fiber at its unique empty slot, as a continuous
linear functional. -/
noncomputable def eval0 (x : M) :
    Tensor0SSpace 0 I x →L[𝕜] 𝕜 :=
  (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (toModelL 0 x)

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval0_apply {x : M} (T : Tensor0SSpace 0 I x) :
    eval0 (𝕜 := 𝕜) (E := E) (I := I) x T = T Fin.elim0 := by
  change (continuousMultilinearCurryFin0 𝕜 E 𝕜)
      (Tensor0SSpace.toModel (I := I) T) = T Fin.elim0
  rw [continuousMultilinearCurryFin0_apply]
  exact congrArg T (Subsingleton.elim _ _)

/-- Embed a covariant tensor fiber as a mixed tensor with zero upper slots.

The resulting continuous linear map sends a `(0,0)` input `c` to
`eval0 c • T`. -/
noncomputable def toRS0 {s : ℕ} {x : M}
    (T : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (eval0 (𝕜 := 𝕜) (E := E) (I := I) x).smulRight T

set_option linter.unusedSectionVars false in
@[simp]
theorem toRS0_apply {s : ℕ} {x : M}
    (T : Tensor0SSpace s I x) (c : Tensor0SSpace 0 I x) :
    toRS0 (𝕜 := 𝕜) (E := E) (I := I) T c =
      c Fin.elim0 • T := by
  rw [toRS0, ContinuousLinearMap.smulRight_apply, eval0_apply]

/-- Construct a `Tensor0SSpace` fiber element from a model fiber element.
This is the inverse of `Tensor0SSpace.toModel`. -/
def ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv s x).symm f

set_option linter.unusedSectionVars false in
@[simp]
theorem toModelL_apply {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModelL s x T = toModel T := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_add {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensor0SSpace_continuousLinearEquiv s x) T₁ T₂

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_smul {s : ℕ} {x : M} (c : 𝕜) (T : Tensor0SSpace s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensor0SSpace_continuousLinearEquiv s x) c T

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_zero {s : ℕ} {x : M} :
    toModel (0 : Tensor0SSpace s I x) = 0 :=
  map_zero (tensor0SSpace_continuousLinearEquiv s x)

@[simp]
theorem toModel_neg {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModel (-T) = -toModel T :=
  map_neg (tensor0SSpace_continuousLinearEquiv s x) T

@[simp]
theorem toModel_sub {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  map_sub (tensor0SSpace_continuousLinearEquiv s x) T₁ T₂

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem ofModel_toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ofModel (toModel T) = T :=
  (tensor0SSpace_continuousLinearEquiv s x).symm_apply_apply T

set_option linter.unusedSectionVars false in
@[simp]
theorem toModel_ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensor0SSpace_continuousLinearEquiv s x).apply_symm_apply f

set_option linter.unusedSectionVars false in
@[simp]
theorem cle_ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    tensor0SSpace_continuousLinearEquiv (I := I) s x
        (ofModel (I := I) (x := x) f) = f :=
  toModel_ofModel (I := I) (x := x) f

omit [FiniteDimensional 𝕜 E] in
theorem toModel_continuous {s : ℕ} {x : M} :
    Continuous (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).continuous_toFun

omit [FiniteDimensional 𝕜 E] in
theorem toModel_injective {s : ℕ} {x : M} :
    Function.Injective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).injective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_surjective {s : ℕ} {x : M} :
    Function.Surjective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).surjective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_bijective {s : ℕ} {x : M} :
    Function.Bijective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).bijective

/-- The unit `(0,0)` tensor in a pointwise tensor fiber. -/
def one0 (x : M) : Tensor0SSpace 0 I x :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜
    (fun _ : Fin 0 => TangentSpace I x) (1 : 𝕜)

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem one0_apply {x : M} (v : Fin 0 → TangentSpace I x) :
    one0 (𝕜 := 𝕜) (I := I) x v = (1 : 𝕜) := by
  rw [one0, ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [FiniteDimensional 𝕜 E] in
/-- A pointwise `(0,0)` tensor is its scalar value times the unit `(0,0)` tensor. -/
theorem eq_smul_one0 {x : M} (c : Tensor0SSpace 0 I x) :
    c = c Fin.elim0 • one0 (𝕜 := 𝕜) (I := I) x := by
  ext v
  change c v = c Fin.elim0 * (one0 (𝕜 := 𝕜) (I := I) x v)
  rw [one0_apply, mul_one]
  exact congrArg c (Subsingleton.elim v Fin.elim0)

end Tensor0SSpace

/-- The fiber `TensorRSSpace r s I x` is continuously linearly isomorphic to
`TensorRSModel r s 𝕜 E`: this follows from `arrowCongr` applied to the
`tensor0SSpace_continuousLinearEquiv` on both the domain and codomain. -/
def tensorRSSpace_continuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpace_continuousLinearEquiv (I := I) s x)

omit [FiniteDimensional 𝕜 E] in
/-- The `→L[𝕜]` between `Tensor0SSpace` fibers (with the bundle topology) is the
same type as `→L[𝕜]` between `ContinuousMultilinearMap` fibers (with the norm topology),
since the topologies agree by `tensor0SSpace_topology_eq`. -/
private theorem tensorRSSpace_type_eq (r s : ℕ) (x : M) :
    TensorRSSpace r s I x =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  unfold TensorRSSpace Tensor0SSpace Bundle.continuousMultilinearMap
  congr 1 <;> exact tensor0SSpace_topology_eq (I := I) _ x

/-- Transport `NormedAddCommGroup` and `NormedSpace` together from the norm-topology type. -/
private def tensorRSSpace_normedInstances (r s : ℕ) (x : M) :
    Σ' (ng : NormedAddCommGroup (TensorRSSpace r s I x)),
      @NormedSpace 𝕜 (TensorRSSpace r s I x) _ ng.toSeminormedAddCommGroup :=
  (tensorRSSpace_type_eq (I := I) r s x) ▸ ⟨inferInstance, inferInstance⟩

/-- The fiber `TensorRSSpace r s I x` is a normed additive commutative group. -/
instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).1

/-- The fiber `TensorRSSpace r s I x` is a normed `𝕜`-module. -/
instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).2

/-- Scalar multiplication on `TensorRSSpace r s I x` is continuous. -/
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TensorRSSpace r s I x))

/-!
## Coercion to Model Fiber

The continuous linear equivalence `tensorRSSpace_continuousLinearEquiv` identifies each fiber
`TensorRSSpace r s I x` with the model fiber `TensorRSModel r s 𝕜 E`. We package this as
`TensorRSSpace.toModel` (forward direction) and `TensorRSSpace.ofModel` (its inverse),
together with linearity, continuity, and invertibility lemmas.
-/

namespace TensorRSSpace

/-- Coerce a `TensorRSSpace` fiber element to the model fiber `TensorRSModel r s 𝕜 E`.
This is the forward direction of `tensorRSSpace_continuousLinearEquiv`. -/
def toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    TensorRSModel r s 𝕜 E :=
  tensorRSSpace_continuousLinearEquiv (I := I) r s x T

/-- `TensorRSSpace.toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap

/-- Construct a `TensorRSSpace` fiber element from a model fiber element.
This is the inverse of `TensorRSSpace.toModel`. -/
def ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm f

set_option linter.unusedSectionVars false in
@[simp]
theorem toModelL_apply {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    (toModelL (I := I) r s x).toFun T = toModel T := rfl

@[simp]
theorem toModel_add {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensorRSSpace_continuousLinearEquiv (I := I) r s x) T₁ T₂

@[simp]
theorem toModel_smul {r s : ℕ} {x : M} (c : 𝕜) (T : TensorRSSpace r s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensorRSSpace_continuousLinearEquiv (I := I) r s x) c T

@[simp]
theorem toModel_zero {r s : ℕ} {x : M} :
    toModel (0 : TensorRSSpace r s I x) = 0 :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_zero

@[simp]
theorem toModel_neg {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    toModel (-T) = -toModel T :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_neg T

@[simp]
theorem toModel_sub {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_sub T₁ T₂

@[simp]
theorem ofModel_toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    ofModel (toModel T) = T :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm_apply_apply T

set_option linter.unusedSectionVars false in
@[simp]
theorem toModel_ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).apply_symm_apply f

theorem toModel_continuous {r s : ℕ} {x : M} :
    Continuous (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).continuous_toFun

theorem toModel_injective {r s : ℕ} {x : M} :
    Function.Injective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).injective

theorem toModel_surjective {r s : ℕ} {x : M} :
    Function.Surjective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).surjective

theorem toModel_bijective {r s : ℕ} {x : M} :
    Function.Bijective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).bijective

end TensorRSSpace

/-!
## Currying
-/

/-- Currying isomorphism: a (0,s+1)-tensor is equivalent to a continuous linear map
from the tangent space to the space of (0,s)-tensors.

The proof composes three continuous linear equivalences:
1. `tensor0SSpace_continuousLinearEquiv` bridges the bundle/norm topology diamond.
2. `continuousMultilinearCurryLeftEquiv` curries the first argument of the multilinear map.
3. `arrowCongr` with the inverse of `tensor0SSpace_continuousLinearEquiv` converts
   the codomain back from norm to bundle topology. -/
noncomputable def tensor0S_curry (s : ℕ) (x : M) :
    Tensor0SSpace (s+1) I x ≃L[𝕜]
    (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) :=
  (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl 𝕜 E).arrowCongr
          (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm))

/-!
## (0,s)-Tensor Bundle Instances

The (0,s) covariant tensor bundle inherits its fiber bundle, vector bundle, and smooth
vector bundle structure from `Bundle.continuousMultilinearMap` applied to the tangent bundle.
-/

/-- The total space of the (0,s)-tensor bundle carries a topology from the
multilinear bundle construction. -/
instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Bundle.continuousMultilinearMap.topologicalSpace_totalSpace 𝕜 s E (TangentSpace I)

/-- The (0,s)-tensor bundle is a fiber bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_fiber (s : ℕ) :
    FiberBundle
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.fiberBundle 𝕜 s E (TangentSpace I)

/-- The (0,s)-tensor bundle is a vector bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    VectorBundle 𝕜
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.vectorBundle 𝕜 s E (TangentSpace I)

/-!
## Smooth Bundle Instances

The smooth bundle instances require `IsManifold I (n + 1) M` to get
`ContMDiffVectorBundle n` for the tangent bundle via `TangentBundle.contMDiffVectorBundle`.
-/

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-- The (0,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
@[simp]
noncomputable instance tensor0SBundle_smooth [CompleteSpace 𝕜] (s : ℕ) :
    ContMDiffVectorBundle n
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) I := by
  haveI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  haveI : (Bundle.continuousMultilinearMap.vectorPrebundle
      𝕜 s E (TangentSpace I : M → Type _)).IsContMDiff I n :=
    Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth s I n
  exact (Bundle.continuousMultilinearMap.vectorPrebundle
    𝕜 s E (TangentSpace I : M → Type _)).contMDiffVectorBundle I

/-!
## (r,s)-Tensor Bundle Instances

The (r,s) tensor bundle is defined as the hom bundle from the (0,r)- to the (0,s)-tensor
bundle, using `Bundle.ContinuousLinearMap`.
-/

/-- The total space of the (r,s)-tensor bundle carries a topology, induced by viewing it
as the hom bundle from the (0,r)- to the (0,s)-tensor bundle. -/
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a fiber bundle, as a hom bundle between two fiber bundles. -/
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundle_topology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a vector bundle with model fiber `TensorRSModel r s 𝕜 E`. -/
noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModel_normedAddCommGroup r s) (tensorRSModel_normedSpace r s) _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (fun (x : M) => Tensor0SSpace r I x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
noncomputable instance tensorRSBundle_smooth [CompleteSpace 𝕜] (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s)
      (tensorRSBundle_vector r s) :=
  ContMDiffVectorBundle.continuousLinearMap

-- Removed: `tensor0S_topologicalSpace_zero` (s = 0 diamond fix).
-- It introduced a total-space topology via `Bundle.Trivial` that was propositionally
-- but not definitionally equal to `tensor0SBundle_topology 0`, blocking FiberBundle
-- instance resolution for the (0,0)-tensor bundle. Resolved with user approval to
-- support P23 (covariant derivative on (0,s)-tensor bundles).

/-!
## Bundle / norm topology bridges for differentiability and smoothness

The CLE `tensor0SSpace_continuousLinearEquiv s x` is the identity at the underlying data
level (its `toFun` is `id`); the diamond between the bundle and norm topologies on the
fiber is closed by `tensor0SSpace_topology_eq`. This means that a section
`T : Π x : M, Tensor0SSpace s I x` and the function `fun y => (CLE) (T y)` are equal as
maps on the underlying carrier, only their target type differs.

This section provides the bridges showing that (m)differentiability/smoothness of a section
through the CLEs `tensor0SSpace_continuousLinearEquiv` and `tensor0S_curry` is equivalent
to (m)differentiability/smoothness of the underlying section.
-/

omit [FiniteDimensional 𝕜 E] in
/-- The forward direction of `tensor0SSpace_continuousLinearEquiv` is the identity function
on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) :
    tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x T = T := rfl

omit [FiniteDimensional 𝕜 E] in
/-- The inverse direction of `tensor0SSpace_continuousLinearEquiv` is the identity function
on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_symm_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).symm T = T := rfl

omit [FiniteDimensional 𝕜 E] in
/-- The CLE coerces to `id` on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_coe (s : ℕ) (x : M) :
    (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x : _ → _) = id := rfl

omit [FiniteDimensional 𝕜 E] in
/-- The inverse CLE coerces to `id` on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_symm_coe (s : ℕ) (x : M) :
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).symm : _ → _) = id := rfl

/-- Applying the mixed-tensor CLE to a tensor and then to the model version of a
covariant input agrees with applying the tensor first and then passing the
output through the covariant CLE. -/
theorem tensorRSSpace_continuousLinearEquiv_apply_apply
    (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (input : Tensor0SSpace r I x) :
    tensorRSSpace_continuousLinearEquiv (I := I) (M := M) r s x T
        (Tensor0SSpace.toModel (I := I) input) =
      Tensor0SSpace.toModel (I := I) (T input) := by
  rfl

/-- Applying the inverse mixed-tensor CLE to a model tensor and then to a
covariant input agrees with applying the model tensor to the model input and
then returning through the covariant inverse CLE. -/
theorem tensorRSSpace_continuousLinearEquiv_symm_apply_apply
    (r s : ℕ) (x : M) (T : TensorRSModel r s 𝕜 E)
    (input : Tensor0SSpace r I x) :
    ((tensorRSSpace_continuousLinearEquiv (I := I) (M := M) r s x).symm T)
        input =
      Tensor0SSpace.ofModel (I := I) (x := x)
        (T (Tensor0SSpace.toModel (I := I) input)) := by
  rfl

namespace Tensor0SSpace

@[simp]
theorem toModel_one0 {x : M} :
    toModel (I := I) (one0 (𝕜 := 𝕜) (I := I) x) =
      Tensor0SModel.one0 (𝕜 := 𝕜) (E := E) := by
  rfl

/-- The natural continuous linear equivalence
`Tensor0SSpace s I x ≃L TensorRSSpace 0 s I x`, obtained by transporting the
model-fiber equivalence through the existing fiber/model equivalences. -/
noncomputable def rs0Equiv {s : ℕ} {x : M} :
    Tensor0SSpace s I x ≃L[𝕜] TensorRSSpace 0 s I x :=
  (tensor0SSpace_continuousLinearEquiv (I := I) s x).trans
    ((Tensor0SModel.rs0Equiv (𝕜 := 𝕜) (E := E) (s := s)).trans
      (tensorRSSpace_continuousLinearEquiv (I := I) (M := M) 0 s x).symm)

set_option linter.unusedSectionVars false in
@[simp]
theorem rs0Equiv_apply {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    rs0Equiv (𝕜 := 𝕜) (E := E) (I := I) (M := M) T =
      toRS0 (𝕜 := 𝕜) (E := E) (I := I) T := by
  apply ContinuousLinearMap.ext
  intro c
  apply toModel_injective (I := I)
  suffices h :
      ofModel (I := I) (x := x) (toModel (I := I) (c Fin.elim0 • T)) =
        c Fin.elim0 • T by
    simpa [rs0Equiv, tensorRSSpace_continuousLinearEquiv_symm_apply_apply,
      Tensor0SModel.toRS0_apply, toRS0_apply, toModel,
      tensor0SSpace_continuousLinearEquiv_apply] using h
  exact ofModel_toModel (I := I) (T := c Fin.elim0 • T)

end Tensor0SSpace

set_option linter.unnecessarySimpa false in
/-- The canonical scalar action on a mixed-tensor fiber is pointwise scalar
action on the underlying continuous-linear-map model. -/
theorem tensorRSSpace_smul_apply
    {r s : ℕ} {x : M} (c : 𝕜) (T : TensorRSSpace r s I x)
    (input : Tensor0SSpace r I x) :
    (c • T) input = c • T input := by
  apply Tensor0SSpace.toModel_injective (I := I)
  have h :=
    congrArg
      (fun F : TensorRSModel r s 𝕜 E =>
        F (Tensor0SSpace.toModel (I := I) input))
      (TensorRSSpace.toModel_smul (I := I) (x := x) c T)
  simpa [TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpace_continuousLinearEquiv_apply_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul] using h

end
end Tensor0SBundle
