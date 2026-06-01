import DifferentialGeometry.Integral.Connection.CovGradParallelNaturality

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

end Connection
end Integral
end DifferentialGeometry

end
