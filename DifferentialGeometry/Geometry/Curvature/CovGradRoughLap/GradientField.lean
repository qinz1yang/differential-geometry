import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality

/-!
# The rough-Laplacian / covariant-gradient commutator (order-`2` Gårding core)

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, this file
develops the third-order Weitzenböck commutator that drives the order-`2`
elliptic-regularity ("Gårding") estimate.

Writing `∇T₀ = covGrad g 0 2 T₀` for the `(0, 3)`-tensor covariant gradient,
`Δ_∇` for the rough (connection) Laplacian, the target commutator says that
applying the rough Laplacian to the gradient field equals taking the gradient of
the rough Laplacian, up to an explicit curvature defect:

```
Δ_∇(∇T₀) (x) = ∇(Δ_∇ T₀) (x) + Curv x.
```

## What this file establishes

* `rawTensorConnLap_covGrad_eq_frame_trace` — the rough Laplacian of the
  `(0, 3)`-tensor gradient field is the frame trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇T₀)` of its
  second covariant derivative over the smooth `g_x`-orthonormal frame (the
  rank-`(0, 3)` instance of the trace identity
  `rawTensorConnLap_eq_frame_trace_secondCovDeriv`).

* `covGrad_apply_unit_eval_generic` — the gradient `covGrad g 0 2 S` of a smooth
  `(0, 2)`-tensor field `S` reads its extra tangent direction off the leftmost
  slot when evaluated at the unit `(0, 0)`-tensor (right-hand side reading).

* `covDeriv_unit_eval_eq` / `covApply_unit_eval_eq` — the unit `(0, 0)`-evaluation
  intertwines the `(0, 3) = (0, 0) → (0, 3)` Hom-bundle covariant derivative
  `tensorCov g 0 3` with the abstract `(0, 3)`-tensor covariant derivative
  `tensor0SCovariantDerivative I M 3 (LeviCivita g)`, with no correction term:
  the unit section is `∇`-parallel.

* `tensorSecondCovDeriv_covGrad_unit_eval` — the **transport** of the
  `(0, 3)` second covariant derivative of `∇T₀`, evaluated at the unit, into the
  abstract `(0, 3)`-tensor second covariant derivative of the unit-evaluated
  gradient field `U y := (∇T₀) y (unit)`. Combined with
  `rawTensorConnLap_covGrad_eq_frame_trace`, this writes the entire left-hand side
  of the target commutator as the abstract `(0, 3)` rough Laplacian of `U`.

## Remaining piece (documented, not assumed)

The target curvature defect `Curv x` is the leftmost-slot reading of the
explicit third-order curvature field `Tensor3rdCurv` of
`TensorThirdOrderWeitzenbock.lean`. Closing the full commutator from the abstract
reduction above is the depth-`3` parallel naturality of the covariant-gradient
bundle equivalence `covGradBundleEquiv`: identifying the abstract `(0, 3)` rough
Laplacian of `U` (whose leftmost slot is the gradient direction, differentiated
through the slot-`0` Christoffel correction) with the `(0, 2)` frame-trace swap
`frame_trace_thirdCovDeriv_swap` of the directionally-derived `T₀`. That
identification is the slot-`0`-Christoffel-vs-field-direction matching; it is the
sole remaining structural input and is not assumed here.

## Sign / convention

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian (the frame trace
`∑ᵢ ∇²_{Bᵢ, Bᵢ}`), matching `TensorThirdOrderWeitzenbock.lean`,
`TensorConnLaplacian.lean`, and `CovGradParallelNaturality.lean`. The covariant
gradient `covGrad g 0 s` curries the new tangent-direction slot as the leftmost
covariant slot, the convention produced by the directional covariant derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The `(0, 3)`-tensor gradient field `covGrad g 0 2 T₀` is smooth in total-space
`mk'` form. This is the smoothness field of the underlying smooth section of the
`SmoothCcTensor`, which is already stated in `T% = mk'` form. -/
lemma covGrad_contMDiff_mk'
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 3 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 3 ℝ E)
        (E := fun z : M => TensorRSSpace 0 3 I z) b
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 2 T₀).toSection.contMDiff

/-- The rough Laplacian of the `(0, 3)`-tensor gradient field is the frame trace
of its second covariant derivative. This is the rank-`(0, 3)` instance of the
trace identity `rawTensorConnLap_eq_frame_trace_secondCovDeriv`, applied to the
underlying section of `covGrad g 0 2 T₀`. -/
lemma rawTensorConnLap_covGrad_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    rawTensorConnLap (I := I) g 0 3
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x :=
  rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

/-- **Unit-evaluation of the gradient of a smooth `(0, 2)`-tensor (right-hand
side).** The `(0, 3)`-tensor `(covGrad g 0 2 S).toSection x`, evaluated at the
unit `(0, 0)`-tensor and on a `Fin 3`-tuple `v`, reads the tangent direction
`v 0` off the leftmost slot: it is the directional covariant derivative
`tensorCovDerivAt g 0 2 S x (v 0)`, applied to the unit tensor and evaluated on
the tail `(v 1, v 2)`. -/
lemma covGrad_apply_unit_eval_generic
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 S x (v 0))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) :=
  covGrad_toSection_apply_eval (I := I) (M := M) g 0 2 S x
    (unitZeroSec (I := I) (M := M) x) v

/-- **Unit-evaluation of the gradient of a smooth `(0, s)`-tensor (general valence).**
The `(0, s + 1)`-tensor `(covGrad g 0 s S).toSection x`, evaluated at the unit
`(0, 0)`-tensor and on a `Fin (s + 1)`-tuple `v`, reads the tangent direction `v 0`
off the leftmost slot: it is the directional covariant derivative
`tensorCovDerivAt g 0 s S x (v 0)`, applied to the unit tensor and evaluated on the
tail `Matrix.vecTail v`. This is the general-valence analogue of
`covGrad_apply_unit_eval_generic` (which is its `s = 2` instance); the proof is the
fully-valence-uniform pointwise-evaluation formula `covGrad_toSection_apply_eval`. -/
lemma covGrad_apply_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s S x (v 0))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) :=
  covGrad_toSection_apply_eval (I := I) (M := M) g 0 s S x
    (unitZeroSec (I := I) (M := M) x) v

/-- **Slot-`0` reading of the unit-evaluated gradient of any smooth `(0, s)`-tensor
field (general valence).** The currying of `(covGrad g 0 s S).toSection x (unit)`
along the slot-`0` tangent direction `w` recovers the directional covariant
derivative of `S`, evaluated at the unit `(0, 0)`-tensor:
```
tensor0S_curry s x ((covGrad g 0 s S).toSection x (unit)) w = (∇_w S)(x)(unit).
```
This is the general-valence analogue of `curry_covGrad_unit_eval` (its `s = 2`
instance). The proof ports verbatim: it combines the general-valence tensor-curry
evaluation `tensor0S_curry_apply_eval` with the general-valence unit-evaluation
`covGrad_apply_unit_eval_genVal`. -/
lemma curry_covGrad_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x w)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x w)
        (unitZeroSec (I := I) (M := M) x)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v0 := w) (vs := m)]
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g s S x (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-- **Unit-evaluation commutes with the `(0, 3)`-covariant derivative.** For an
arbitrary smooth `Cₛ^∞` `(0, 3)`-tensor section `σ`, the directional
`(0, 3)`-tensor covariant derivative of `σ` along `v`, applied to the unit
`(0, 0)`-tensor, equals the abstract `(0, 3)`-tensor covariant derivative of the
unit-evaluated section `y ↦ σ y (unit)`:
```
(∇^{(0,3)}_v σ)(x)(unit) = (∇^{(0,3)}_v (y ↦ σ y (unit)))(x).
```
The product rule against the parallel unit `(0, 0)`-section has no correction
term, exactly as in `covGrad_covDeriv_at_unit_eq`. -/
lemma covDeriv_unit_eval_eq
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

/-- **Unit-evaluation commutes with the `(0, s)`-covariant derivative (general valence).**
For an arbitrary smooth `Cₛ^∞` `(0, s)`-tensor section `σ`, the directional `(0, s)`-tensor
covariant derivative of `σ` along `v`, applied to the unit `(0, 0)`-tensor, equals the
abstract `(0, s)`-tensor covariant derivative of the unit-evaluated section `y ↦ σ y (unit)`:
```
(∇^{(0,s)}_v σ)(x)(unit) = (∇^{(0,s)}_v (y ↦ σ y (unit)))(x).
```
The product rule against the parallel unit `(0, 0)`-section has no correction term. This is
the general-valence analogue of `covDeriv_unit_eval_eq` (its `s = 3` instance); the proof is
verbatim, the directional version of `tensorRSCovariantDerivative_apply` against the parallel
unit (`tensor0SCovariantDerivative_unitZero_eq_zero`). (Reproduced here rather than imported
from the on-disk `tensorRSCovariantDerivative_zeroS_unit_eval`, which lives downstream.) -/
lemma covDeriv_unit_eval_eq_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

/-- **Unit-evaluation intertwines `covApply`.** For a smooth `Cₛ^∞`
`(0, 3)`-tensor section `σ` and a smooth tangent vector field `X`, the
unit-evaluation of `covApply (tensorCov g 0 3) X σ` equals `covApply
(tensor0SCovariantDerivative I M 3 (LeviCivita g)) X` of the unit-evaluated
section `y ↦ σ y (unit)`, as dependent functions of the base point. -/
lemma covApply_unit_eval_eq
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        covApply (tensorCov (I := I) g 0 3) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq (I := I) (M := M) g σ y (X y)

/-- The directionally-derived gradient field `covApply (tensorCov g 0 3) X
(covGrad g 0 2 T₀)` packaged as a smooth `Cₛ^∞` `(0, 3)`-tensor section, for a
smooth tangent vector field `X`. Its smoothness is the bundle-generic
`covApplyRS_contMDiff` applied to the smooth gradient field. -/
noncomputable def covApplyCovGradSection
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 3
      (covGrad_contMDiff_mk' (I := I) (M := M) g T₀) hX)

@[simp] lemma covApplyCovGradSection_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSection (I := I) (M := M) g T₀ hX y =
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y := rfl

/-- The **unit-evaluated gradient field** `U y := (covGrad g 0 2 T₀) y (unit)`,
the `(0, 3)`-valued section whose value on a `Fin 3`-tuple reads the leftmost slot
as the tangent direction of the directional covariant derivative of `T₀`. This is
the section that the abstract `(0, 3)`-tensor covariant derivative
`tensor0SCovariantDerivative I M 3` differentiates in the transported commutator. -/
noncomputable def unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
      (unitZeroSec (I := I) (M := M) y)

@[simp] lemma unitGradField_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (y : M) :
    unitGradField (I := I) (M := M) g T₀ y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

/-- **Transport of the `(0, 3)` second covariant derivative through the unit.**
For smooth tangent vector fields `B`, the second covariant derivative
`tensorSecondCovDeriv g 0 3 B B (covGrad g 0 2 T₀)` of the gradient field,
evaluated at the unit `(0, 0)`-tensor, equals the abstract `(0, 3)`-tensor second
covariant derivative of the unit-evaluated gradient field `U`:
```
(∇²_{B, B}(∇T₀))(x)(unit)
  = ∇^{(0,3)abs}_B(∇^{(0,3)abs}_B U)(x) − ∇^{(0,3)abs}_{(∇_B B)(x)} U (x).
```
The right-hand side is the abstract `(0, 3)`-tensor second covariant derivative of
`U` along `B`. -/
lemma tensorSecondCovDeriv_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorSecondCovDeriv (I := I) g 0 3 B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) B
            (unitGradField (I := I) (M := M) g T₀)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · have hσ : (fun y : M => covApplyCovGradSection (I := I) (M := M) g T₀ hB y) =
        (fun y : M => covApply (tensorCov (I := I) g 0 3) B
          (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y) := by
      funext y; exact covApplyCovGradSection_apply (I := I) (M := M) g T₀ hB y
    have h1 := covDeriv_unit_eval_eq (I := I) (M := M) g
      (covApplyCovGradSection (I := I) (M := M) g T₀ hB) x (B x)
    simp only [covApplyCovGradSection_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

/-! ### General-valence currying tower

The lemmas below port the `(0, 2) → (0, 3)` currying/transport apparatus above to an
arbitrary covariant valence `(0, s) → (0, s + 1)`, and assemble the **two-slot evaluation
bridge** `tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal`: the genuine tensorial
second covariant derivative of a smooth `(0, s)`-tensor `S` along a smooth field, evaluated
at the unit, is the two-leftmost-slot reading of the second iterated covariant gradient
`∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`. Every cited primitive is already
valence-uniform; the only `s`-specialised input is the slot-`0` Hom-bundle product rule
`abstract_succ_covDeriv_unfold_at` (`AbstractRoughLaplacian.lean`, fixed valence `3`), whose
fully `s`-uniform proof is reproduced here as `abstract_succ_covDeriv_unfold_at_genVal`
(that file imports this one, so the general statement is reproduced rather than imported). -/

/-- **Slot-`0` Christoffel exposure for the abstract `(0, s + 1)` covariant derivative
(general valence).** For a smooth `(0, s + 1)`-tensor section `W` and smooth vector fields
`Vfield`, `Y`, the slot-`0` curry of the directional abstract covariant derivative
`cov_{s+1}.toFun W x (Vfield x)`, read on the slot-`0` direction `Y x`, decomposes by the
Hom-bundle product rule as
```
(curry cov_{s+1}.toFun W x (Vfield x))(Y x)
  = cov_s.toFun (y ↦ curry W_y (Y y)) x (Vfield x) − (curry W_x)((∇^{TM}_{Vfield} Y)(x)).
```
This is the fully valence-uniform analogue of `abstract_succ_covDeriv_unfold_at` (its
`s = 2` instance); the proof is verbatim, the `succ` decomposition of the abstract
`(0, s + 1)`-tensor covariant derivative composed with the Hom-bundle product rule
`homBundleCovariantDerivativeFun_apply_eq`. -/
theorem abstract_succ_covDeriv_unfold_at_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π y : M, Tensor0SSpace (s + 1) I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) s x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x (Vfield x) -
        Tensor0SNabla.curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel s ℝ E)
    (V := fun z : M => Tensor0SSpace s I z)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (τ := Tensor0SNabla.curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0S_curry (I := I) (M := M) s x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel s ℝ E)
        (V := fun z : M => Tensor0SSpace s I z)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (τ := Tensor0SNabla.curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivative_succ I M (LeviCivita (I := I) g)
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_eq]]
    rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) s x).apply_symm_apply _
  rw [hsucc]
  exact hHom

/-- **The unit-evaluated gradient field (general valence)** `U y := (covGrad g 0 s S) y (unit)`,
the `(0, s + 1)`-valued section whose slot-`0` curry along `w` reads the directional covariant
derivative `(∇_w S)(y)(unit)` (`curry_covGrad_unit_eval_genVal`). This is the general-valence
analogue of `unitGradField`. -/
noncomputable def unitGradFieldGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    Π y : M, Tensor0SSpace (s + 1) I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      (covGrad (I := I) (M := M) g 0 s S).toSection y)
      (unitZeroSec (I := I) (M := M) y)

@[simp] lemma unitGradFieldGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (y : M) :
    unitGradFieldGen (I := I) (M := M) g s S y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        (covGrad (I := I) (M := M) g 0 s S).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

/-- **Smoothness of the general-valence unit-evaluated gradient field.** `U := unitGradFieldGen
g s S` is a smooth section of the `(0, s + 1)`-tensor bundle, as the application of the smooth
gradient Hom-bundle section `covGrad g 0 s S` to the smooth unit `(0, 0)`-section. General-valence
analogue of `contMDiff_unitGradField`. -/
lemma contMDiff_unitGradFieldGen (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        (unitGradFieldGen (I := I) (M := M) g s S y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covGrad (I := I) (M := M) g 0 s S).toSection y))) :=
    (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace (s + 1) I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel (s + 1) ℝ E) hϕ hv

/-- **Smoothness of the curried general-valence unit-evaluated gradient field.** The curried
Hom-bundle section `y ↦ tensor0S_curry s y (U y)` of `U := unitGradFieldGen g s S` is smooth as a
section of the Hom-bundle `TM →L[ℝ] T^{(0,s)}`. General-valence analogue of
`contMDiff_curried_unitGradField`. -/
lemma contMDiff_curried_unitGradFieldGen (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) y)) :=
  (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradFieldGen (I := I) (M := M) g s S)).mp
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S)

/-- **Slot-`0` reading of the unit-evaluated gradient field (general valence).** The slot-`0`
curry of `U y := unitGradFieldGen g s S y` along `w` recovers the directional covariant
derivative of `S`, evaluated at the unit:
```
(curry U_y)(w) = tensor0S_curry s y (U y) w = (∇_w S)(y)(unit).
```
General-valence analogue of `curry_unitGradField_eq`. Immediate from
`curry_covGrad_unit_eval_genVal`. -/
lemma curry_unitGradFieldGen_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (y : M) (w : TangentSpace I y) :
    Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) y w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        tensorCovDerivAt (I := I) (M := M) g 0 s S y w)
        (unitZeroSec (I := I) (M := M) y) := by
  rw [Tensor0SNabla.curriedSection_apply, unitGradFieldGen_apply]
  exact curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S y w

/-- **Smoothness of the `(0, s + 1)`-tensor gradient field in mk' form (general valence).**
General-valence analogue of `covGrad_contMDiff_mk'`. The gradient `covGrad g 0 s S` is a
`SmoothCcTensor g 0 (s + 1)`; its underlying section is smooth in total-space `mk'` form. -/
lemma covGrad_contMDiff_mk'_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b
        ((covGrad (I := I) (M := M) g 0 s S).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff

/-- The directionally-derived gradient field `covApply (tensorCov g 0 (s + 1)) X
(covGrad g 0 s S)` packaged as a smooth `Cₛ^∞` `(0, s + 1)`-tensor section (general valence).
General-valence analogue of `covApplyCovGradSection`; smoothness is `covApplyRS_contMDiff`
applied to the smooth gradient field. The total-space fibre-bundle instances for the symbolic
valence `s + 1` are supplied explicitly (`tensorRSBundle_topology`/`tensorRSBundle_fiber`),
matching the codebase pattern, since typeclass search stalls on the `Nat.succ` head. -/
noncomputable def covApplyCovGradSection_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    @ContMDiffSection ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
      (fun y : M => TensorRSSpace 0 (s + 1) I y)
      (Tensor0SBundle.tensorRSBundle_topology 0 (s + 1)) (fun _ => inferInstance)
      (Tensor0SBundle.tensorRSBundle_fiber 0 (s + 1)) :=
  @ContMDiffSection.mk ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
    (fun y : M => TensorRSSpace 0 (s + 1) I y)
    (Tensor0SBundle.tensorRSBundle_topology 0 (s + 1)) (fun _ => inferInstance)
    (Tensor0SBundle.tensorRSBundle_fiber 0 (s + 1))
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 (s + 1)
      (covGrad_contMDiff_mk'_genVal (I := I) (M := M) g s S) hX)

@[simp] lemma covApplyCovGradSection_genVal_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSection_genVal (I := I) (M := M) g s S hX y =
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y := rfl

/-- **Unit-evaluation intertwines `covApply` (general valence).** For a smooth `Cₛ^∞`
`(0, t)`-tensor section `σ` and a smooth tangent vector field `X`, the unit-evaluation of
`covApply (tensorCov g 0 t) X σ` equals `covApply (tensor0SCovariantDerivative I M t
(LeviCivita g)) X` of the unit-evaluated section `y ↦ σ y (unit)`, as dependent functions of
the base point. General-valence analogue of `covApply_unit_eval_eq` (its `t = 3` instance);
the valence is a bare variable `t`, so the consumer instantiates it at `t = s + 1`. -/
lemma covApply_unit_eval_eq_genVal
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from
        covApply (tensorCov (I := I) g 0 t) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g t σ y (X y)

/-- **Transport of the `(0, s + 1)` second covariant derivative through the unit (general
valence).** For smooth tangent vector fields `B`, the second covariant derivative
`tensorSecondCovDeriv g 0 (s + 1) B B (covGrad g 0 s S)` of the gradient field, evaluated at
the unit `(0, 0)`-tensor, equals the abstract `(0, s + 1)`-tensor second covariant derivative
of the unit-evaluated gradient field `U := unitGradFieldGen g s S`. General-valence analogue of
`tensorSecondCovDeriv_covGrad_unit_eval` (its `s = 2` instance); the proof ports verbatim, the
slot-uniform `tensorSecondCovDeriv` definition combined with the general-valence unit-transport
`covDeriv_unit_eval_eq_genVal` and `covApply_unit_eval_eq_genVal`. -/
lemma tensorSecondCovDeriv_covGrad_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
              (LeviCivita (I := I) g)) B
            (unitGradFieldGen (I := I) (M := M) g s S)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldGen (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · have h1 := covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covApplyCovGradSection_genVal (I := I) (M := M) g s S hB) x (B x)
    simp only [covApplyCovGradSection_genVal_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

/-- **Two-slot evaluation bridge (general valence).** The genuine tensorial second covariant
derivative `tensorSecondCovDeriv g 0 s X Y S` of a smooth `(0, s)`-tensor `S` along smooth fields
`X, Y`, evaluated at the unit `(0, 0)`-tensor and on a `Fin s`-tuple `m`, is the
**two-leftmost-slot reading** of the second iterated covariant gradient
`∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)` at `(X x, Y x)`:
```
toModel (∇²S(x)(unit)) (X x ::ᵥ Y x ::ᵥ m) = toModel (tensorSecondCovDeriv g 0 s X Y S (x)(unit)) m.
```
This is the foundational identity "second covariant gradient = second covariant derivative",
made precise through the unit-evaluation; it is the general-valence assembly of the currying
tower. The proof reads the two leftmost (gradient) slots of `∇²S` off as iterated directional
covariant derivatives (`covGrad_toSection_apply_eval`, `tensorCovDerivAt_def`,
`tensorRSCovariantDerivative_apply`/`tensorRSCovariantDerivative_zeroS_unit_eval` for the
parallel unit), unfolds the slot-`0` Christoffel correction of the abstract derivative
(`abstract_succ_covDeriv_unfold_at_genVal`), and matches it against the
`tensorSecondCovDeriv` definition (`tensorSecondCovDeriv_def`,
`tensorRSCovariantDerivative_zeroS_unit_eval`), the slot-`0` reading of each piece being
`curry_unitGradFieldGen_eq` / `curry_covGrad_unit_eval_genVal`. -/
theorem tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g 0 s X Y (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x))
        m := by
  classical

  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS

  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g (s + 1) GS x
    (Fin.cons (X x) (Fin.cons (Y x) m))]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons (X x) (Fin.cons (Y x) m) ∘ Fin.succ) = Fin.cons (Y x) m from
    funext (fun j => by simp [Fin.cons_succ])]

  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) GS x (X x))
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (X x) from by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 (s + 1) GS x (X x)]
    exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1) GS.toSection x (X x)]

  rw [show Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldGen (I := I) (M := M) g s S) x (X x))
        (Fin.cons (Y x) m) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
            (unitGradFieldGen (I := I) (M := M) g s S) x (X x)) (Y x)) m from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (X x)) (v0 := Y x) (vs := m)).symm]

  rw [abstract_succ_covDeriv_unfold_at_genVal (I := I) (M := M) g s
    (unitGradFieldGen (I := I) (M := M) g s S) (Vfield := X) (Y := Y) (x := x)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]

  rw [show (fun y : M => Tensor0SNabla.curriedSection I M
        (unitGradFieldGen (I := I) (M := M) g s S) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          tensorCovDerivAt (I := I) (M := M) g 0 s S y (Y y))
          (unitZeroSec (I := I) (M := M) y)) from
    funext (fun y => curry_unitGradFieldGen_eq (I := I) (M := M) g s S y (Y y))]
  rw [curry_unitGradFieldGen_eq (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun Y x (X x))]

  rw [tensorSecondCovDeriv_def (I := I) g 0 s X Y (fun y : M => S.toSection y) x]

  refine congrArg (fun T : Tensor0SSpace s I x => Tensor0SSpace.toModel T m) ?_

  rw [ContinuousLinearMap.sub_apply]

  have houter :
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
              tensorCovDerivAt (I := I) (M := M) g 0 s S y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) x (X x))
          (unitZeroSec (I := I) (M := M) x) := by
    set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
      ContMDiffSection.mk
        (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
        (covApplyRS_contMDiff (I := I) g 0 s
          (T := fun z : M => S.toSection z) S.toSection.contMDiff (X := Y) hY) with hσ
    have hσapp : ∀ y : M, σ y =
        covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y := fun y => rfl
    rw [show (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) =
        (fun y : M => σ y) from funext (fun y => (hσapp y).symm)]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x (X x)]
    refine congrArg (fun F : Π z : M, Tensor0SSpace s I z =>
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun F x (X x)) ?_
    funext y
    rw [hσapp y, covApply_apply, ← tensorCovDerivAt_def (I := I) (M := M) g 0 s S y (Y y)]

  have hchr :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s S x ((LeviCivita (I := I) g).toFun Y x (X x))]
  rw [houter, hchr]

end Connection
end Integral
end DifferentialGeometry

end
