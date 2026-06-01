import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorClose2

/-!
# The `(0, 2) → (0, 3)` rough-Laplacian / covariant-gradient commutator:
the moving-frame residual isolation

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the order-`2`
covariant Gårding estimate needs the commutator of the rough (connection) Laplacian
with the covariant gradient,
```
Δ_∇(∇T₀) = ∇(Δ_∇ T₀) + Curv,
```
with an explicit curvature defect `Curv : SmoothCcTensor g 0 3` and a first-order
Sobolev `L²` bound on `Curv`.

This file packages the commutator equation `hcomm` for the canonical defect
`Curv := Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` (the difference of the two `(0, 3)`-tensor fields),
and isolates — as a single concrete, named, smooth `(0, 3)`-tensor field — the
**moving-frame residual** that the remaining curvature reconciliation must control.

## The two concrete frame-trace readings

The right-hand-side reading `covGrad_rawConnLap_unit_eval_curry`
(`CovGradRoughLapCommutatorClose2.lean`) gives the slot-`0` curry, along a tangent
direction `w`, of the unit-`(0, 0)`-evaluation of `∇(Δ_∇ T₀)`:
```
tensor0S_curry 2 x (∇(Δ_∇T₀) x (unit)) w = (∇_w Δ_∇T₀)(x)(unit),
```
where `Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀` is the **moving-frame** rough
Laplacian (its frame `Cᶻ_i := smoothOrthoFrame g z i` is `g_z`-orthonormal at each
`z`).

The frame-trace swap `frame_trace_third_eq_swap_unit`
(`CovGradRoughLapCommutatorClose2.lean`) isolates the explicit third-order curvature
field `Tensor3rdCurv` from a **fixed-at-`x`** frame trace: with `W := smoothExtensionTangent x w`
and `B_i := smoothOrthoFrame g x i`,
```
(∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit)
  = (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit) + Tensor3rdCurv g 0 2 W T₀ x (unit).
```
The frame `B_i` is `g_x`-orthonormal only at `z = x`; for `z ≠ x` it is *not* the
moving-frame `Cᶻ_i`, so `∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀ (x)` and `∇_w(Δ_∇T₀)(x)` differ by a
frame-derivative correction.

## What this file establishes

* `covGradRoughLapMovingFrameResidual` — the **explicit moving-frame residual**: the
  concrete `(0, 3)`-tensor field whose unit-evaluation, curried along `w`, is the
  difference of the moving-frame right-hand-side reading `(∇_w Δ_∇T₀)(x)(unit)` and the
  fixed-frame swapped trace `(∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit)`. Both differenced
  terms are second-covariant-derivative-order in `T₀`, so the residual is controlled by
  `‖∇²T₀‖`.

* `covGradRoughLapCurv` — the canonical commutator defect `Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` as a
  `SmoothCcTensor g 0 3`.

* `covGradRoughLap_commutator_eq` — the **commutator equation** `hcomm`:
  `Δ_∇(∇T₀) = ∇(Δ_∇ T₀) + covGradRoughLapCurv g T₀`, by `sub_add_cancel`. This is the
  exact `hcomm` consumed by `secondCovGrad_l2NormSq_le_rawConnLap_gen`
  (`TensorConnLapSecondOrderGardingGen.lean`).

* `rhs_curry_eq_swap_add_curv_add_residual` — the **right-hand-side curried-unit
  decomposition** of `∇(Δ_∇ T₀)`:
  ```
  (∇_w Δ_∇T₀)(x)(unit)
    = (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit)
      + (moving-frame residual, curried along w).
  ```
  This is `covGrad_rawConnLap_unit_eval_curry` rewritten through the definition of the
  residual; it isolates the residual as the single concrete object the curvature
  reconciliation must bound.

## The precise remaining gap (documented, not assumed)

Closing `hcurv` — the first-order Sobolev `L²` bound
`‖covGradRoughLapCurv g T₀‖_{L²} ≤ C₀ (‖T₀‖ + ‖∇T₀‖ + ‖∇²T₀‖)` — reduces, by the
unit-extensionality `tensor03_ext_unit` and the curried readings above, to two
genuinely-distinct pointwise fibre-norm bounds, both within the `‖∇²T₀‖`-budget that
`secondCovGrad_l2NormSq_le_rawConnLap_gen` admits via Young's inequality:

1. **`Tensor3rdCurv` fibre-norm bound.** The four summands of `Tensor3rdCurv` are the
   curvature contractions `R(Bᵢ, W)(∇_{Bᵢ} T₀)`, `∇_{Bᵢ}(R(Bᵢ, W) T₀)` and the bracket
   terms `∇_{[Bᵢ, W]}(∇_{Bᵢ} T₀)`, `∇_{Bᵢ}(∇_{[Bᵢ, W]} T₀)`, controlled fibrewise by
   `‖T₀‖`, `‖∇T₀‖`, `‖∇²T₀‖` via the committed curvature contraction bounds
   (`Tensor3rdCurvFiberNormBound.lean`).

2. **The moving-frame residual fibre-norm bound.** `covGradRoughLapMovingFrameResidual`
   is the difference of the moving-frame and fixed-frame second-covariant-derivative
   frame traces; the frame variation `z ↦ smoothOrthoFrame g z i − smoothOrthoFrame g x i`
   vanishes to first order at `x`, so its `w`-derivative against the second covariant
   derivative of `T₀` is controlled by `‖∇²T₀‖` (uniform on the compact `M`).

In addition, the **slot-`0` Christoffel-vs-field-direction matching** (the
`CovGradRoughLapCommutatorClose2.lean` obstruction 1) is needed to identify the
commutator left-hand side `Δ_∇(∇T₀)(x)(unit)` (curried along `w`) with
`(∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit) + (Christoffel families)`; only after that
identification does `covGradRoughLapCurv` equal `Tensor3rdCurv + residual` as a curried
identity. That matching is **not** performed here — this file isolates the residual and
packages the commutator equation, leaving the matching and the two fibre-norm bounds as
the remaining work.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (the frame trace), matching
`CovGradRoughLapCommutatorClose2.lean` and `TensorThirdOrderWeitzenbock.lean`. The
covariant gradient `covGrad g 0 s` curries the new tangent-direction slot as the
leftmost covariant slot.
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

variable {E : Type*} [NormedAddCommGroup E]
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

/-- **The canonical commutator defect.** The difference of the rough Laplacian of the
`(0, 3)`-tensor gradient field and the gradient of the rough Laplacian, as a smooth
compactly-supported `(0, 3)`-tensor field:
```
covGradRoughLapCurv g T₀ := Δ_∇(∇T₀) − ∇(Δ_∇ T₀).
```
It is the canonical witness for the commutator equation consumed by the generalized
order-`2` Gårding estimate. -/
noncomputable def covGradRoughLapCurv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 3 :=
  rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) -
    covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)

/-- **The commutator equation** (`hcomm`). For the canonical defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)`,
```
Δ_∇(∇T₀) = ∇(Δ_∇ T₀) + covGradRoughLapCurv g T₀,
```
by `sub_add_cancel`. This is the exact `hcomm` hypothesis consumed by
`secondCovGrad_l2NormSq_le_rawConnLap_gen` (`TensorConnLapSecondOrderGardingGen.lean`). -/
theorem covGradRoughLap_commutator_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) =
      covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)
        + covGradRoughLapCurv (I := I) (M := M) g T₀ := by
  rw [covGradRoughLapCurv]
  rw [add_comm]
  rw [sub_add_cancel]

/-- **The fixed-at-`x` swapped frame trace at the unit.** With `W := smoothExtensionTangent
x w` and `B_i := smoothOrthoFrame g x i`, this is the unit-`(0, 0)`-evaluation of the
fixed-frame trace `∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀`:
```
(∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit).
```
It is the term that `frame_trace_third_eq_swap_unit` pairs with `Tensor3rdCurv`. -/
noncomputable def fixedFrameSwapTraceUnit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (tensorCov (I := I) g 0 2).toFun
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))) x
        (smoothExtensionTangent (I := I) x w x))
    (unitZeroSec (I := I) (M := M) x)

/-- **The moving-frame residual at the unit.** With `W := smoothExtensionTangent x w`,
`B_i := smoothOrthoFrame g x i`, and `Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀` the
moving-frame rough Laplacian, this is the `(0, 2)`-tensor difference of the moving-frame
right-hand-side reading and the fixed-frame swapped trace:
```
covGradRoughLapMovingFrameResidual g T₀ x w
  := (∇_w Δ_∇T₀)(x)(unit) − (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit).
```
Both terms are second-covariant-derivative-order frame traces of `T₀`; their difference
is the frame-variation correction governing the moving-vs-fixed frame discrepancy. -/
noncomputable def covGradRoughLapMovingFrameResidual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
      (unitZeroSec (I := I) (M := M) x) -
    fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w

/-- Defining identity for `covGradRoughLapMovingFrameResidual`. -/
lemma covGradRoughLapMovingFrameResidual_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
          (unitZeroSec (I := I) (M := M) x) -
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w := rfl

/-- **Right-hand-side curried-unit decomposition.** The moving-frame right-hand-side
reading `(∇_w Δ_∇T₀)(x)(unit)` equals the fixed-frame swapped trace
`(∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit)` plus the moving-frame residual:
```
(∇_w Δ_∇T₀)(x)(unit)
  = (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit)
    + covGradRoughLapMovingFrameResidual g T₀ x w.
```
This isolates the moving-frame residual as the single concrete `(0, 2)`-tensor correction
the curvature reconciliation must control. -/
theorem rhs_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
        (unitZeroSec (I := I) (M := M) x) =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGradRoughLapMovingFrameResidual_def]
  rw [add_comm]
  rw [sub_add_cancel]

/-- **Slot-`0` curry of the gradient of the rough Laplacian, via the residual.** The
slot-`0` curry of the unit-`(0, 0)`-evaluation of `∇(Δ_∇ T₀) = covGrad g 0 2
(rawTensorConnLapSmooth g 0 2 T₀)`, read along `w`, equals the fixed-frame swapped trace
plus the moving-frame residual:
```
tensor0S_curry 2 x (∇(Δ_∇T₀) x (unit)) w
  = (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit)
    + covGradRoughLapMovingFrameResidual g T₀ x w.
```
This is `covGrad_rawConnLap_unit_eval_curry` followed by `rhs_curry_eq_swap_add_residual`;
it is the right-hand-side reading in the form the curvature reconciliation consumes. -/
theorem covGrad_rawConnLap_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  exact rhs_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w

/-- **Frame-trace of `∇_W T₀`, via the gradient-of-Laplacian reading.** With
`W := smoothExtensionTangent x w` and `B_i := smoothOrthoFrame g x i`, the unit-`(0, 0)`-
evaluation of the fixed-frame trace `∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)` equals the slot-`0` curry of
the gradient-of-Laplacian reading minus the moving-frame residual, plus `Tensor3rdCurv`:
```
(∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit)
  = tensor0S_curry 2 x (∇(Δ_∇T₀) x (unit)) w
    − covGradRoughLapMovingFrameResidual g T₀ x w
    + Tensor3rdCurv g 0 2 W T₀ x (unit).
```
This is `frame_trace_third_eq_swap_unit` with the fixed-frame swapped trace rewritten by
`covGrad_rawConnLap_curry_eq_swap_add_residual`. The left-hand side
`∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)` is the curried form to which the commutator left-hand
side `Δ_∇(∇T₀)(x)(unit)` reduces *after* the slot-`0` Christoffel matching. -/
theorem frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g 0 2
              (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          Tensor3rdCurv (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  rw [frame_trace_third_eq_swap_unit (I := I) (M := M) g T₀ x w]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) =
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w from rfl]
  rw [show fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w =
        tensor0S_curry (I := I) (M := M) 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              (covGrad (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
              (unitZeroSec (I := I) (M := M) x)) w -
          covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w from by
      rw [covGrad_rawConnLap_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w]
      rw [add_sub_cancel_right]]

end Connection
end Integral
end DifferentialGeometry

end
