/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Curry
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

/-!
## Point-wise Fibers
-/

/-- The fiber of the (0,s) covariant tensor bundle at `x ∈ M`, defined as
`Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`.

Declared as a non-reducible `def` so that typeclass synthesis treats it as an opaque
type at the `Tensor0SSpace` level. Instances on `Bundle.continuousMultilinearMap` are
re-declared here on `Tensor0SSpace` directly to avoid diamonds when these instances
interact with the bundle / hom-bundle topologies further downstream. -/
@[nolint unusedArguments]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x

/-!
## Bedrock instances for `Tensor0SSpace`

Since `Tensor0SSpace` is now a non-reducible `def`, instances on
`Bundle.continuousMultilinearMap` do not automatically transfer. We re-declare the
needed instances here so they live at the `Tensor0SSpace` level. -/

instance tensor0SSpace_topologicalSpace (s : ℕ) (x : M) :
    TopologicalSpace (Tensor0SSpace s I x) :=
  inferInstanceAs (TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_addCommGroup (s : ℕ) (x : M) :
    AddCommGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (AddCommGroup (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_module (s : ℕ) (x : M) :
    Module 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_isTopologicalAddGroup (s : ℕ) (x : M) :
    IsTopologicalAddGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (IsTopologicalAddGroup
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_continuousAdd (s : ℕ) (x : M) :
    ContinuousAdd (Tensor0SSpace s I x) :=
  inferInstanceAs (ContinuousAdd
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_continuousSMul (s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_t2Space (s : ℕ) (x : M) :
    T2Space (Tensor0SSpace s I x) :=
  inferInstanceAs (T2Space (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_moduleFree (s : ℕ) (x : M) :
    Module.Free 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module.Free 𝕜
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_instFunLike (s : ℕ) (x : M) :
    FunLike (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 :=
  inferInstanceAs (FunLike
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x) _ _)

omit [FiniteDimensional 𝕜 E] in
/-- Extensionality for `Tensor0SSpace`. Since the type is a non-reducible `def`, Lean
cannot find the underlying `ContinuousMultilinearMap.ext` automatically; we re-export it
at the `Tensor0SSpace` level. -/
@[ext]
theorem tensor0SSpace_ext (s : ℕ) (x : M)
    {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → TangentSpace I x, T v = T' v) : T = T' :=
  ContinuousMultilinearMap.ext (M₁ := fun _ : Fin s => TangentSpace I x) (M₂ := 𝕜) h

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.zero_apply (s : ℕ) (x : M)
    (v : Fin s → TangentSpace I x) :
    (0 : Tensor0SSpace s I x) v = 0 := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.add_apply (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (A + B) v = A v + B v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.smul_apply (s : ℕ) (x : M)
    (c : 𝕜) (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (c • A) v = c • A v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.nsmul_apply (s : ℕ) (x : M)
    (n : ℕ) (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (n • A) v = n • A v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.neg_apply (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (-A) v = -A v := by
  rw [show -A = (-1 : 𝕜) • A by exact (neg_one_smul 𝕜 A).symm,
    Tensor0SSpace.smul_apply, neg_one_smul]

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.sub_apply (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (A - B) v = A v - B v := by
  rw [sub_eq_add_neg, Tensor0SSpace.add_apply, Tensor0SSpace.neg_apply,
    sub_eq_add_neg]

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.sum_apply {α : Type*} (t : Finset α) (s : ℕ) (x : M)
    (A : α → Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (∑ i ∈ t, A i) v = ∑ i ∈ t, A i v := by
  classical
  induction t using Finset.induction with
  | empty => simp only [Finset.sum_empty, Tensor0SSpace.zero_apply]
  | insert a t ha =>
      simp only [Finset.sum_insert ha, Tensor0SSpace.add_apply, *]

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.domDomCongr_apply {s s' : ℕ} {x : M}
    (e : Fin s ≃ Fin s') (A : Tensor0SSpace s I x)
    (v : Fin s' → TangentSpace I x) :
    (ContinuousMultilinearMap.domDomCongr e A) v = A (fun i => v (e i)) := rfl

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_update_smul {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x)
    (i : Fin s) (c : 𝕜) (v : TangentSpace I x) :
    A (Function.update m i (c • v)) = c • A (Function.update m i v) :=
  ContinuousMultilinearMap.map_update_smul A m i c v

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_update_add {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x)
    (i : Fin s) (v w : TangentSpace I x) :
    A (Function.update m i (v + w)) =
      A (Function.update m i v) + A (Function.update m i w) :=
  ContinuousMultilinearMap.map_update_add A m i v w

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_smul_univ {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (c : Fin s → 𝕜)
    (v : Fin s → TangentSpace I x) :
    A (fun i => c i • v i) = (∏ i, c i) • A v :=
  ContinuousMultilinearMap.map_smul_univ A c v

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_sum {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) {α : Fin s → Type*}
    [∀ i, Fintype (α i)]
    (g : ∀ i, α i → TangentSpace I x) :
    A (fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, A (fun i => g i (r i)) :=
  ContinuousMultilinearMap.map_sum A g

/-- `NormedAddCommGroup` on `Tensor0SSpace s I x` inherited from the bundle's CMM fiber.

NOTE: the `TopologicalSpace` inside this instance is the **norm topology** on
`ContinuousMultilinearMap`, while `tensor0SSpace_topologicalSpace` (registered separately)
is the **bundle topology**. The two agree by `tensor0SSpace_topology_eq` but are not
definitionally equal — this is the same propositional-vs-definitional topology mismatch
present in Mathlib's `Bundle.continuousMultilinearMap.instNormedAddCommGroup`. It does not
cause downstream synthesis problems for users who rely on `tensor0SSpace_topologicalSpace`
for the bundle topology and on the operator-norm instances purely as a normed-space
witness. -/
instance tensor0SSpace_normedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (NormedAddCommGroup
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

instance tensor0SSpace_normedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (NormedSpace 𝕜
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

/-- The cotangent space at `x ∈ M`: linear functionals on the tangent space,
realized as (0,1)-tensors. -/
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace 1 I x

/-- The fiber of the (r,s)-tensor bundle at `x ∈ M`: continuous linear maps from
(0,r)-tensors to (0,s)-tensors, using `(V⊗W)* ≅ V*⊗W*` and `V*⊗W ≅ Hom(V,W)`.

Declared as a non-reducible `def`; instances are re-derived explicitly below. -/
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[nolint unusedArguments]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

/-!
## Bedrock instances for `TensorRSSpace`

`TensorRSSpace r s I x` is `Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x`. Since it is
also a non-reducible `def`, we re-declare the basic instances explicitly. The base
instances are sourced from the underlying `→L[𝕜]` type; the normed instances are
transported from the model fiber and share the same underlying additive structure
through `tensorRSSpace_continuousLinearEquiv`. -/

instance tensorRSSpace_topologicalSpace (r s : ℕ) (x : M) :
    TopologicalSpace (TensorRSSpace r s I x) :=
  inferInstanceAs (TopologicalSpace (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_addCommGroup (r s : ℕ) (x : M) :
    AddCommGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (AddCommGroup (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_module (r s : ℕ) (x : M) :
    Module 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_isTopologicalAddGroup (r s : ℕ) (x : M) :
    IsTopologicalAddGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (IsTopologicalAddGroup
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_continuousAdd (r s : ℕ) (x : M) :
    ContinuousAdd (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousAdd (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_moduleFree [CompleteSpace 𝕜] (r s : ℕ) (x : M) :
    Module.Free 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module.Free 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

/-- `FunLike` instance for `TensorRSSpace`, enabling direct function-style application of an
`(r,s)`-tensor on a `(0,r)`-tensor to obtain a `(0,s)`-tensor. -/
instance tensorRSSpace_instFunLike (r s : ℕ) (x : M) :
    FunLike (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (FunLike (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) _ _)

/-- `ContinuousLinearMapClass` instance for `TensorRSSpace`, providing additivity, continuity,
and scalar-multiplicativity of the function-style application. -/
instance tensorRSSpace_instContinuousLinearMapClass (r s : ℕ) (x : M) :
    ContinuousLinearMapClass (TensorRSSpace r s I x) 𝕜
      (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (ContinuousLinearMapClass
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) 𝕜 _ _)

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem TensorRSSpace.zero_apply (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x) :
    (0 : TensorRSSpace r s I x) A = 0 := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem TensorRSSpace.add_apply (r s : ℕ) (x : M)
    (T U : TensorRSSpace r s I x) (A : Tensor0SSpace r I x) :
    (T + U) A = T A + U A := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem TensorRSSpace.smul_apply (r s : ℕ) (x : M)
    (c : 𝕜) (T : TensorRSSpace r s I x) (A : Tensor0SSpace r I x) :
    (c • T) A = c • T A := rfl

/-- A `TensorRSSpace` element converted to a `ContinuousLinearMap`. Since the underlying
type is `Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x`, this is just the identity. -/
def TensorRSSpace.toCLM {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x := T

/-- A `ContinuousLinearMap` converted to a `TensorRSSpace` element. -/
def TensorRSSpace.ofCLM {r s : ℕ} {x : M}
    (T : Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) : TensorRSSpace r s I x := T

omit [FiniteDimensional 𝕜 E] in
/-- Extensionality for `TensorRSSpace`. Since the type is a non-reducible `def`, Lean
cannot find the underlying `ContinuousLinearMap.ext` automatically; we re-export it
at the `TensorRSSpace` level. -/
@[ext]
theorem tensorRSSpace_ext (r s : ℕ) (x : M)
    {T T' : TensorRSSpace r s I x}
    (h : ∀ v : Tensor0SSpace r I x,
      (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T) v =
      (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T') v) : T = T' :=
  ContinuousLinearMap.ext
    (f := (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T))
    (g := (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T')) h

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
  inferInstanceAs
    (FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x))

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  (Bundle.continuousMultilinearMap.finrank_eq (𝕜 := 𝕜) (F := E)
    (E := (TangentSpace I : M → Type _)) s x :)

/-- `TensorRSModel r s 𝕜 E` is finite-dimensional over `𝕜`. Provided as an explicit instance to
short-circuit the lengthy typeclass-synthesis chain through `ContinuousLinearMap.finiteDimensional`
applied to the `Tensor0SModel` factors, which can exceed the default heartbeat budget at
downstream call sites. -/
noncomputable instance tensorRSModel_finiteDimensional [CompleteSpace 𝕜] (r s : ℕ) :
    FiniteDimensional 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  haveI : FiniteDimensional 𝕜 (Tensor0SModel r 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional s
  exact ContinuousLinearMap.finiteDimensional

/-- The dimension of `TensorRSModel r s 𝕜 E` over `𝕜` is `(finrank 𝕜 E) ^ (r + s)`. -/
@[simp]
theorem finrank_tensorRSModel [CompleteSpace 𝕜] (r s : ℕ) :
    Module.finrank 𝕜 (TensorRSModel r s 𝕜 E) = (Module.finrank 𝕜 E) ^ (r + s) := by
  haveI : FiniteDimensional 𝕜 (Tensor0SModel r 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional s
  haveI : Module.Free 𝕜 (Tensor0SModel s 𝕜 E) := inferInstance
  have e : (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) ≃ₗ[𝕜]
      (Tensor0SModel r 𝕜 E →ₗ[𝕜] Tensor0SModel s 𝕜 E) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank 𝕜 (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) =
      (Module.finrank 𝕜 E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap 𝕜 𝕜,
    finrank_continuousMultilinearMap r, finrank_continuousMultilinearMap s, ← pow_add]

/-- The fiber `TensorRSSpace r s I x` is finite-dimensional over `𝕜`. Provided as an explicit
instance to short-circuit the lengthy typeclass-synthesis chain through
`ContinuousLinearMap.finiteDimensional` applied to the `Tensor0SSpace` factors. -/
noncomputable instance tensorRSSpace_finiteDimensional [CompleteSpace 𝕜] (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.finiteDimensional

/-- The dimension of the fiber `TensorRSSpace r s I x` over `𝕜` is `(finrank 𝕜 E) ^ (r + s)`. -/
@[simp]
theorem finrank_tensorRSSpace [CompleteSpace 𝕜] (r s : ℕ) (x : M) :
    Module.finrank 𝕜 (TensorRSSpace r s I x) = (Module.finrank 𝕜 E) ^ (r + s) := by
  haveI : Module.Free 𝕜 (Tensor0SSpace s I x) := inferInstance
  have e : (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) ≃ₗ[𝕜]
      (Tensor0SSpace r I x →ₗ[𝕜] Tensor0SSpace s I x) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) =
      (Module.finrank 𝕜 E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap 𝕜 𝕜,
    finrank_tensor0SSpace r x, finrank_tensor0SSpace s x, ← pow_add]

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

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_neg {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModel (-T) = -toModel T :=
  map_neg (tensor0SSpace_continuousLinearEquiv s x) T

omit [FiniteDimensional 𝕜 E] in
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

end Tensor0SSpace

/-- The fiber `TensorRSSpace r s I x` is continuously linearly isomorphic to
`TensorRSModel r s 𝕜 E`: this follows from `arrowCongr` applied to the
`tensor0SSpace_continuousLinearEquiv` on both the domain and codomain. -/
def tensorRSSpace_continuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E := by
  unfold TensorRSSpace
  exact (tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
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

/-- An `AddMonoidHom` view of `tensorRSSpace_continuousLinearEquiv`: forwarding via
the canonical `AddCommGroup` on `TensorRSSpace r s I x` (provided by
`tensorRSSpace_addCommGroup`). Used to induce normed structure compatibly with the
already-installed additive structure, avoiding an `AddCommGroup` diamond. -/
private def tensorRSSpace_toModelAddHom (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →+ TensorRSModel r s 𝕜 E :=
  { toFun := fun T => tensorRSSpace_continuousLinearEquiv (I := I) r s x T
    map_zero' := map_zero (tensorRSSpace_continuousLinearEquiv (I := I) r s x)
    map_add' := map_add (tensorRSSpace_continuousLinearEquiv (I := I) r s x) }

/-- The fiber `TensorRSSpace r s I x` is a normed additive commutative group. The norm is
pulled back from the model fiber `TensorRSModel r s 𝕜 E` along
`tensorRSSpace_continuousLinearEquiv`; the underlying `AddCommGroup` is the canonical
one from `tensorRSSpace_addCommGroup`, so there is no additive-structure diamond.

NOTE: as with `Tensor0SSpace`, the `TopologicalSpace` carried inside this
`NormedAddCommGroup` is induced from the norm, while the explicit
`tensorRSSpace_topologicalSpace` is induced from the fiber-bundle structure. The two
agree by `tensor0SSpace_topology_eq` componentwise but are not definitionally equal. -/
noncomputable instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  NormedAddCommGroup.induced (TensorRSSpace r s I x) (TensorRSModel r s 𝕜 E)
    (tensorRSSpace_toModelAddHom (I := I) r s x)
    (tensorRSSpace_continuousLinearEquiv (I := I) r s x).injective

/-- The fiber `TensorRSSpace r s I x` is a normed `𝕜`-module. Pulled back from the model
fiber along `tensorRSSpace_continuousLinearEquiv`. -/
noncomputable instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) where
  norm_smul_le := by
    intro c T
    change ‖tensorRSSpace_continuousLinearEquiv (I := I) r s x (c • T)‖ ≤
      ‖c‖ * ‖tensorRSSpace_continuousLinearEquiv (I := I) r s x T‖
    rw [map_smul]
    exact norm_smul_le c (tensorRSSpace_continuousLinearEquiv (I := I) r s x T)

/-- Scalar multiplication on `TensorRSSpace r s I x` is continuous. -/
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

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

/-- Helper: `IsManifold I (∞ + 1) M` from `IsManifold I ∞ M`. Needed because Lean's
typeclass synthesis does not normalize `∞ + 1 = ∞`, which is required by
`tensor0SBundle_smooth` and `tensorRSBundle_smooth` when called with `n = ∞`. -/
instance isManifold_infty_succ [IsManifold I ∞ M] :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  have h : ((∞ : WithTop ℕ∞) + 1) = ∞ := by simp
  rw [h]; infer_instance


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

end
end Tensor0SBundle
