import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.VectorBundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# The covariant-gradient bundle equivalence

The covariant derivative of an `(r, s)`-tensor section adds one covariant
(tangent-input) slot, so the pointwise directional covariant derivative of an
`(r, s)`-tensor is naturally an `(r, s + 1)`-tensor. Concretely the pointwise
directional covariant derivative is a continuous linear map from a tangent
vector to an `(r, s)`-tensor, i.e. an element of the fibre of the
covariant-gradient bundle

`Hom(TM, T^{(r,s)} M)`,

whereas an `(r, s + 1)`-tensor lives in the fibre of `T^{(r,s+1)} M`. This file
constructs the canonical identification of these two bundles, both fibrewise as
a continuous linear equivalence and globally as a smooth vector-bundle
equivalence.

## Main definitions

* `Tensor0SBundle.covGradBundleEquiv r s x` — the fibrewise continuous linear
  equivalence `(TangentSpace I x →L[ℝ] TensorRSSpace r s I x) ≃L[ℝ]
  TensorRSSpace r (s + 1) I x`. The extra covariant slot of the
  `(r, s + 1)`-tensor is the slot carrying the tangent-vector input, placed as
  the *leftmost* covariant slot — exactly the convention produced by the
  directional covariant derivative.
* `Tensor0SBundle.covGradModelEquiv r s` — the model-fibre continuous linear
  equivalence `(E →L[ℝ] TensorRSModel r s ℝ E) ≃L[ℝ] TensorRSModel r (s + 1) ℝ E`.
* `Tensor0SBundle.covGradBundleSmoothEquiv r s` — the smooth vector-bundle
  equivalence between the covariant-gradient bundle `Hom(TM, T^{(r,s)})` and the
  `(r, s + 1)`-tensor bundle, covering the identity of the base manifold.

## Construction

Fibrewise, `TensorRSSpace r s I x` unfolds to
`Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x`, so the covariant-gradient fibre
is the iterated hom space

`TangentSpace I x →L[ℝ] (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)`.

Swapping the two outer arrows (Mathlib's `ContinuousLinearMap.flipₗᵢ`) turns this
into

`Tensor0SSpace r I x →L[ℝ] (TangentSpace I x →L[ℝ] Tensor0SSpace s I x)`,

and the project's currying equivalence `tensor0S_curry s x` identifies the inner
factor `TangentSpace I x →L[ℝ] Tensor0SSpace s I x` with `Tensor0SSpace (s+1) I x`.
Post-composing with that equivalence yields
`Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s+1) I x = TensorRSSpace r (s + 1) I x`.

The smooth bundle equivalence is assembled with
`ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv`: in a local trivialisation
the total-space map reduces to the constant model equivalence
`covGradModelEquiv`, which is `C^∞`, so both the forward and inverse total-space
maps are smooth.

## Tags

tensor, covariant derivative, gradient, smooth vector bundle, fiberwise equivalence
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Model-fibre equivalence

The covariant-gradient model fibre `E →L[ℝ] TensorRSModel r s ℝ E` is identified
with the `(r, s + 1)`-tensor model fibre by swapping the outer hom arrows and
currying the new tangent slot into the `(0, s)`-multilinear factor. -/

/-- The model-fibre continuous linear equivalence underlying the
covariant-gradient bundle equivalence.

It identifies the covariant-gradient model fibre
`E →L[ℝ] TensorRSModel r s ℝ E`, i.e.
`E →L[ℝ] (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)`, with the
`(r, s + 1)`-tensor model fibre `TensorRSModel r (s + 1) ℝ E`, i.e.
`Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E`. The first step swaps the
outer arrows; the second step curries the tangent slot into the
`(0, s + 1)`-multilinear factor via `continuousMultilinearCurryLeftEquiv`. -/
def covGradModelEquiv (r s : ℕ) :
    (E →L[ℝ] TensorRSModel r s ℝ E) ≃L[ℝ] TensorRSModel r (s + 1) ℝ E :=
  (ContinuousLinearMap.flipₗᵢ ℝ E (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (Tensor0SModel r ℝ E)).arrowCongr
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (s + 1) => E) ℝ).symm.toContinuousLinearEquiv)

/-- Applying `covGradModelEquiv` to a covariant-gradient model element `Φ`,
evaluated at a `(0, r)`-model tensor `D` and a `Fin (s + 1)`-tuple `v`, equals
evaluating the swapped-and-curried map: `Φ (v 0) D` at the tail of `v`. -/
theorem covGradModelEquiv_apply (r s : ℕ)
    (Φ : E →L[ℝ] TensorRSModel r s ℝ E) (D : Tensor0SModel r ℝ E)
    (v : Fin (s + 1) → E) :
    covGradModelEquiv (E := E) r s Φ D v = Φ (v 0) D (Matrix.vecTail v) := by
  rfl

/-- Applying the inverse of `covGradModelEquiv` to an `(r, s + 1)`-model tensor
`T`, evaluated at a tangent vector `w`, a `(0, r)`-model tensor `D` and a
`Fin s`-tuple `v`, equals `T D (Fin.cons w v)`. -/
theorem covGradModelEquiv_symm_apply (r s : ℕ)
    (T : TensorRSModel r (s + 1) ℝ E) (w : E) (D : Tensor0SModel r ℝ E)
    (v : Fin s → E) :
    (covGradModelEquiv (E := E) r s).symm T w D v = T D (Fin.cons w v) := by
  rfl

/-! ## Fibrewise equivalence

The fibrewise equivalence is built exactly as `covGradModelEquiv`, but on the
bundle fibres `Tensor0SSpace`/`TangentSpace` and using the project's currying
equivalence `tensor0S_curry`. -/

/-- **The covariant-gradient bundle equivalence (fibrewise).**

A continuous linear map from a tangent vector to an `(r, s)`-tensor is the same
data as an `(r, s + 1)`-tensor: the extra covariant slot is the slot carrying
the tangent-vector input. This is the fibre at `x` of the identification of the
covariant-gradient bundle `Hom(TM, T^{(r,s)})` with the `(r, s + 1)`-tensor
bundle.

It is the conjugate of the model-fibre equivalence `covGradModelEquiv` by the
trivialisation-free fibre identifications `tensorRSSpace_continuousLinearEquiv`
(on the codomain factors) and the identity tangent identification (on the
domain factor). The extra covariant slot of the resulting `(r, s + 1)`-tensor is
placed as the *leftmost* covariant slot of the underlying `(0, s + 1)`-
multilinear factor — the convention produced by the directional covariant
derivative `tensorCovDerivAt`, which curries the tangent direction as its first
argument. -/
def covGradBundleEquiv (r s : ℕ) (x : M) :
    (TangentSpace I x →L[ℝ] TensorRSSpace r s I x) ≃L[ℝ]
      TensorRSSpace r (s + 1) I x :=
  ((ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).arrowCongr
      (tensorRSSpace_continuousLinearEquiv (I := I) r s x)).trans
    ((covGradModelEquiv (E := E) r s).trans
      (tensorRSSpace_continuousLinearEquiv (I := I) r (s + 1) x).symm)

set_option backward.isDefEq.respectTransparency true in
/-- Closed form of the forward map: `covGradBundleEquiv r s x Φ` is obtained by
pushing `Φ` to the model fibre, applying `covGradModelEquiv`, and pulling back. -/
theorem covGradBundleEquiv_apply (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x) :
    covGradBundleEquiv (I := I) (M := M) r s x Φ =
      TensorRSSpace.ofModel
        (covGradModelEquiv (E := E) r s
          (((tensorRSSpace_continuousLinearEquiv (I := I) r s x : _ →L[ℝ] _).comp
            Φ : TangentSpace I x →L[ℝ] TensorRSModel r s ℝ E))) :=
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Closed form of the inverse map: `(covGradBundleEquiv r s x).symm T` is
obtained by pushing `T` to the model fibre, applying `(covGradModelEquiv).symm`,
and pulling back the resulting covariant-gradient model element. -/
theorem covGradBundleEquiv_symm_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x) :
    (covGradBundleEquiv (I := I) (M := M) r s x).symm T =
      ((tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I x).comp
        ((covGradModelEquiv (E := E) r s).symm
          (TensorRSSpace.toModel T)) :=
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Evaluating the `(r, s + 1)`-tensor `covGradBundleEquiv r s x Φ` at a
`(0, r)`-tensor `D` and a `Fin (s + 1)`-tuple `v` recovers `Φ (v 0) D (tail v)`:
the tangent direction is read off the first (leftmost) slot. -/
theorem covGradBundleEquiv_apply_eval (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) r s x Φ) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ (v 0)) D)
        (Matrix.vecTail v) := by
  rw [covGradBundleEquiv_apply (I := I) (M := M) r s x Φ]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Evaluating the inverse: the covariant-gradient fibre element
`(covGradBundleEquiv r s x).symm T`, taken along `w` and applied to a
`(0, r)`-tensor `D`, gives the `(0, s)`-tensor whose value at a `Fin s`-tuple `v`
is `T D (cons w v)`. -/
theorem covGradBundleEquiv_symm_apply_eval (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x) (w : TangentSpace I x)
    (D : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T) w) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D)
        (Fin.cons w v) := by
  rw [covGradBundleEquiv_symm_apply (I := I) (M := M) r s x T]
  rfl

/-! ## Trivialisation compatibility

To promote `covGradBundleEquiv` to a smooth bundle equivalence we show that, in a
local trivialisation, the total-space map reduces to the constant model
equivalence `covGradModelEquiv`. The covariant-gradient bundle
`Hom(TM, T^{(r,s)})` and the `(r, s + 1)`-tensor bundle `Hom(0r, 0(s+1))` are
both `Bundle.ContinuousLinearMap` bundles, so their trivialisations are computed
by `Bundle.Trivialization.continuousLinearMap_apply`. -/

section Trivialisation

variable [CompleteSpace ℝ]

/-- The chart trivialisation base set of every tensor bundle considered here
coincides with the tangent-bundle chart base set: all are `(chartAt H α).source`.
This identifies the common domain on which the trivialisation-compatibility
identities hold. -/
private theorem tensorRSBundle_baseSet_eq (r s : ℕ) (α : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (trivializationAt E (TangentSpace I) α).baseSet := by
  change (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  exact Set.inter_self _

/-- The chart trivialisation base set of the covariant-gradient bundle
`Hom(TM, T^{(r,s)})` coincides with the tangent-bundle chart base set. -/
private theorem covGradBundle_baseSet_eq (r s : ℕ) (α : M) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α).baseSet =
      (trivializationAt E (TangentSpace I) α).baseSet := by
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  rw [tensorRSBundle_baseSet_eq (I := I) r s α, Set.inter_self]

/-! ### Trivialisation-fibre evaluation

On the chart base set, the trivialisation-fibre coordinate of a `(0, n)`-tensor
bundle element, evaluated at a tuple of model vectors, equals the underlying
multilinear map evaluated at the tuple of tangent vectors pulled back through the
tangent-bundle trivialisation. -/

open TensorMultilinear in
/-- The chart-`α` trivialisation-fibre of a `(0, n)`-tensor bundle element
`⟨b, X⟩`, evaluated at a model tuple `v` (using the `FunLike` action of the
model fibre `Tensor0SModel n ℝ E`), equals `X` evaluated at the tuple of model
vectors pulled back through the tangent-bundle trivialisation. -/
private theorem tensor0S_trivFibre_apply (n : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α).baseSet)
    (X : Tensor0SSpace n I b) (v : Fin n → E) :
    (trivializationAt (Tensor0SModel n ℝ E)
        (fun x : M => Tensor0SSpace n I x) α ⟨b, X⟩).2 v =
      Tensor0SSpace.toModel X
        (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ b (v j)) := by
  have hX : X = (tensor0SSpace_continuousLinearEquiv (I := I) n b).symm
      (Tensor0SSpace.toModel X) :=
    (Tensor0SSpace.ofModel_toModel X).symm
  have hkey := tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) α b hb
    (Tensor0SSpace.toModel X) v
  have hlm : (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α ⟨b, X⟩).2 =
    (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α).linearMapAt ℝ b X := by
    rw [Trivialization.coe_linearMapAt_of_mem _ hb]
  rw [hlm]
  conv_lhs => rw [hX]
  exact hkey

/-! ### The trivialisation-compatibility identity

The trivialisation-fibre of the transformed total-space map equals the constant
model equivalence applied to the trivialisation-fibre of the original. Both hom
bundles have trivialisation-fibre computed by
`Bundle.Trivialization.continuousLinearMap_apply`; the identity then reduces, by
extensionality, to the trivialisation-fibre evaluation lemma
`tensor0S_trivFibre_apply` for the `(0, r)`, `(0, s)`, and `(0, s + 1)` tensor
bundles, and the slot bookkeeping `Matrix.vecTail`. -/

set_option maxHeartbeats 1600000 in
open TensorMultilinear in
/-- **Trivialisation compatibility.** On the chart-`α` base set, the chart-`α`
trivialisation-fibre of `⟨b, covGradBundleEquiv r s b Φ⟩` (in the
`(r, s + 1)`-tensor bundle) equals `covGradModelEquiv r s` applied to the
chart-`α` trivialisation-fibre of `⟨b, Φ⟩` (in the covariant-gradient bundle).

This is the local reduction of the covariant-gradient bundle equivalence to the
constant model equivalence. -/
theorem covGradBundleEquiv_trivializationAt_eq (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 =
      covGradModelEquiv (E := E) r s
        ((trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
          ⟨b, Φ⟩).2) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) := tensor0SBundle_topology s
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) := tensor0SBundle_topology (s + 1)
  have hb_r : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x) α).baseSet := hb
  have hb_s : b ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) α).baseSet := hb
  have hb_s1 : b ∈ (trivializationAt (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x) α).baseSet := hb
  -- Reduce to an equality of `(0, r)-model → (0, s + 1)-model` continuous linear maps.
  apply ContinuousLinearMap.ext
  intro D
  -- Reduce to an equality of `(0, s + 1)`-model tensors, evaluated at every tuple.
  apply ContinuousMultilinearMap.ext
  intro v
  -- The `(r, s + 1)`-tensor bundle is the hom bundle of the `(0, r)`- and
  -- `(0, s + 1)`-tensor bundles; expand its trivialisation-fibre.
  have hLHS_fibre :
      (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 =
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (s + 1) I b from
            covGradBundleEquiv (I := I) (M := M) r s b Φ).comp
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b)) := rfl
  -- The covariant-gradient bundle is the hom bundle of the tangent bundle and the
  -- `(r, s)`-tensor bundle; expand its trivialisation-fibre.
  have hG_fibre :
      (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) := rfl
  -- The `(r, s)`-tensor bundle is the hom bundle of the `(0, r)`- and
  -- `(0, s)`-tensor bundles; expand its trivialisation-fibre.
  have hRS_fibre : ∀ Ψ : TensorRSSpace r s I b,
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨b, Ψ⟩).2 =
      ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Ψ).comp
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b)) :=
    fun Ψ => rfl
  -- `continuousLinearMapAt` agrees with the trivialisation-fibre on the base set.
  have hclmAt_r : ∀ Z : Tensor0SSpace r I b,
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_r]
  have hclmAt_s : ∀ Z : Tensor0SSpace s I b,
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_s]
  have hclmAt_s1 : ∀ Z : Tensor0SSpace (s + 1) I b,
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_s1]
  have hclmAt_RS : ∀ Ψ : TensorRSSpace r s I b,
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Ψ =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨b, Ψ⟩).2 := by
    intro Ψ
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ (show b ∈ _ from
        (tensorRSBundle_baseSet_eq (I := I) r s α).symm ▸ hb)]
  -- Abbreviation for the `(0, r)`-tensor obtained by trivialising back `D`.
  set Dr : Tensor0SSpace r I b :=
    (trivializationAt (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b D with hDr
  -- Compute the left-hand side.
  have hLHS :
      (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 D v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
        (Matrix.vecTail
          (fun j : Fin (s + 1) =>
            (trivializationAt E (TangentSpace I) α).symmL ℝ b (v j))) := by
    rw [hLHS_fibre]
    change ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b)
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (s + 1) I b from
            covGradBundleEquiv (I := I) (M := M) r s b Φ) Dr) v = _
    rw [hclmAt_s1, tensor0S_trivFibre_apply (I := I) (M := M) (s + 1) α hb_s1]
    rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r s b Φ Dr]
  -- Compute the right-hand side.
  have hRHS :
      covGradModelEquiv (E := E) r s
        ((trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
          ⟨b, Φ⟩).2) D v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
        (fun j : Fin s =>
          (trivializationAt E (TangentSpace I) α).symmL ℝ b
            (Matrix.vecTail v j)) := by
    rw [covGradModelEquiv_apply]
    rw [hG_fibre]
    change ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))))
        D (Matrix.vecTail v) = _
    rw [hclmAt_RS, hRS_fibre]
    change ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b)
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
          (Matrix.vecTail v) = _
    rw [hclmAt_s, tensor0S_trivFibre_apply (I := I) (M := M) s α hb_s]
  rw [hLHS, hRHS]
  congr 1

/-- **Trivialisation compatibility (inverse direction).** On the chart-`α` base
set, the chart-`α` trivialisation-fibre of `⟨b, (covGradBundleEquiv r s b).symm T⟩`
(in the covariant-gradient bundle) equals `(covGradModelEquiv r s).symm` applied
to the chart-`α` trivialisation-fibre of `⟨b, T⟩` (in the `(r, s + 1)`-tensor
bundle). -/
theorem covGradBundleEquiv_symm_trivializationAt_eq (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSSpace r (s + 1) I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, (covGradBundleEquiv (I := I) (M := M) r s b).symm T⟩).2 =
      (covGradModelEquiv (E := E) r s).symm
        ((trivializationAt (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) α ⟨b, T⟩).2) := by
  have hforward := covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb
    ((covGradBundleEquiv (I := I) (M := M) r s b).symm T)
  rw [(covGradBundleEquiv (I := I) (M := M) r s b).apply_symm_apply T] at hforward
  rw [hforward, ContinuousLinearEquiv.symm_apply_apply]

end Trivialisation

/-! ## The smooth bundle equivalence

The total-space maps of `covGradBundleEquiv` and its inverse are `C^∞`: in a
chart trivialisation each reduces to the constant model equivalence
`covGradModelEquiv` (resp. its inverse) by the trivialisation-compatibility
identities. Packaging the fibrewise equivalences with these two smoothness facts
through `ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv` yields the smooth
vector-bundle equivalence. -/

section SmoothEquiv

variable [CompleteSpace ℝ]

set_option maxHeartbeats 1600000 in
/-- The total-space map of `covGradBundleEquiv` is `C^∞`. In a chart
trivialisation it reduces, by `covGradBundleEquiv_trivializationAt_eq`, to the
constant model equivalence `covGradModelEquiv` applied to the trivialisation-
fibre of the identity section. -/
theorem covGradBundleEquiv_contMDiff_totalSpace (r s : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
      (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun p : TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) =>
        (⟨p.1, covGradBundleEquiv (I := I) (M := M) r s p.1 p.2⟩ :
          TotalSpace (TensorRSModel r (s + 1) ℝ E)
            (fun y : M => TensorRSSpace r (s + 1) I y))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
        𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E) ∞
        (fun p => (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := (covGradModelEquiv (E := E) r s).toContinuousLinearMap)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt E (TangentSpace I) p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) p₀.proj)
    ] with p hp
    exact covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s p₀.proj hp
      p.snd

set_option maxHeartbeats 1600000 in
/-- The total-space map of the inverse of `covGradBundleEquiv` is `C^∞`. In a
chart trivialisation it reduces, by `covGradBundleEquiv_symm_trivializationAt_eq`,
to the constant inverse model equivalence `(covGradModelEquiv).symm`. -/
theorem covGradBundleEquiv_symm_contMDiff_totalSpace (r s : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E))
      (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun p : TotalSpace (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) =>
        (⟨p.1, (covGradBundleEquiv (I := I) (M := M) r s p.1).symm p.2⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))) := by
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun y : M => TensorRSSpace r (s + 1) I y)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E))
        𝓘(ℝ, TensorRSModel r (s + 1) ℝ E) ∞
        (fun p => (trivializationAt (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := (covGradModelEquiv (E := E) r s).symm.toContinuousLinearMap)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt E (TangentSpace I) p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y))).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) p₀.proj)
    ] with p hp
    exact covGradBundleEquiv_symm_trivializationAt_eq (I := I) (M := M) r s p₀.proj hp
      p.snd

/-- **The covariant-gradient bundle equivalence (smooth, global).**

The covariant-gradient bundle `Hom(TM, T^{(r,s)})` — whose fibre at `x` carries
the pointwise directional covariant derivative of an `(r, s)`-tensor section — is
`C^∞`-isomorphic, as a vector bundle covering the identity of `M`, to the
`(r, s + 1)`-tensor bundle. Fibrewise the isomorphism is `covGradBundleEquiv`. -/
noncomputable def covGradBundleSmoothEquiv (r s : ℕ) :=
  letI : NormedAddCommGroup (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (s + 1)
  letI : NormedSpace ℝ (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedSpace r (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  (ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => (covGradBundleEquiv (I := I) (M := M) r s x).toLinearEquiv)
    (covGradBundleEquiv_contMDiff_totalSpace (I := I) (M := M) r s)
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r s) :
      ContMDiffVectorBundleEquiv ℝ I ∞
        (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)
        (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y))

/-- The smooth bundle equivalence `covGradBundleSmoothEquiv` covers the identity
map of the base manifold `M`. -/
theorem covGradBundleSmoothEquiv_baseMap (r s : ℕ) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).baseMap = id :=
  rfl

/-- The fibrewise linear equivalence of `covGradBundleSmoothEquiv` at `x` is the
fibrewise covariant-gradient equivalence `covGradBundleEquiv r s x`. -/
theorem covGradBundleSmoothEquiv_fiberLinearEquiv (r s : ℕ) (x : M) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).fiberLinearEquiv x =
      (covGradBundleEquiv (I := I) (M := M) r s x).toLinearEquiv :=
  rfl

/-- The total-space map of `covGradBundleSmoothEquiv` acts fibrewise by
`covGradBundleEquiv`. -/
theorem covGradBundleSmoothEquiv_toDiffeomorph_apply (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ⟨x, Φ⟩ =
      ⟨x, covGradBundleEquiv (I := I) (M := M) r s x Φ⟩ :=
  rfl

end SmoothEquiv

end Tensor0SBundle

end
