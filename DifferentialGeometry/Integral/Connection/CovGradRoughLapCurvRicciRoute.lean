import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorClose3
import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Connection.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpHigherRankParseval

/-!
# The curried curvature-defect identity, reduced to the slot-`0` frame-trace matching

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` Gårding
commutator defect is
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)   (a `(0, 3)`-tensor field),
```
(`CovGradRoughLapCommutatorClose3.lean`). Its pointwise fibre-norm bound — the hypothesis
`hpt` of `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
(`CovGradRoughLapCurvL2Bound.lean`) — is the only remaining ingredient for the unconditional
order-`2` covariant Gårding estimate.

## The curvature route

The genuine third-order-tensor Weitzenböck curvature reconciliation is already proved as the
section-level **curvature commutator** `frame_trace_thirdCovDeriv_swap`
(`TensorThirdOrderWeitzenbock.lean`): commuting the fixed-`x` orthonormal frame trace
`∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}` past the extra covariant direction `W` introduces exactly the explicit
curvature field `Tensor3rdCurv` (whose summands are Riemann contractions `R(Bᵢ, W)(∇_{Bᵢ} T₀)`,
`∇_{Bᵢ}(R(Bᵢ, W) T₀)` and torsion-free bracket terms). The bracket/`[Bᵢ, W]` handling and the
curvature extraction are internal to that swap; they need not be re-derived.

Wired through the unit `(0, 0)`-evaluation and the slot-`0` curry along `w` (with
`W := smoothExtensionTangent x w`), the **right-hand side** `∇(Δ_∇ T₀)` reading is already in
place:
```
tensor0S_curry 2 x (∇(Δ_∇ T₀) x (unit)) w
  = (∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit) + residual − Tensor3rdCurv g 0 2 W T₀ x (unit),
```
which is `frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv`
(`CovGradRoughLapCommutatorClose3.lean`) re-read through `covGrad_rawConnLap_unit_eval_curry`.
The **left-hand side** `Δ_∇(∇T₀)` reading is `rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap`
followed by `curry_unitGradAbstractRoughLap_along`
(`CovGradRoughLapCommutatorClose2.lean`).

## What this file establishes

* `slot0FrameTraceMatching` — the **named slot-`0` frame-trace matching predicate**: the
  unit-`(0, 0)`-evaluation of `Δ_∇(∇T₀)`, curried along the gradient direction `w`, equals the
  fixed-frame iterated-covariant trace `(∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit)`. This is precisely
  the torsion-free **slot-`0` Christoffel matching** documented as the single remaining
  obstruction in `CovGradRoughLapCommutatorClose{2,3}.lean`; it is curvature-free (no
  `riemannSec` occurs — the curvature lives entirely in `Tensor3rdCurv`, supplied by the
  already-proved swap).

* `covGradRoughLapCurv_curry_eq_of_slot0Matching` — the headline **curried curvature-defect
  identity**, derived from `slot0FrameTraceMatching`: the unit-`(0, 0)`-evaluation of the
  canonical defect `covGradRoughLapCurv g T₀`, curried along `w`, equals the explicit curvature
  field `Tensor3rdCurv g 0 2 W T₀ x (unit)` minus the moving-frame residual
  `covGradRoughLapMovingFrameResidual g T₀ x w`. This isolates the genuine third-order tensor
  Weitzenböck content as a single concrete curvature contraction plus the explicit residual —
  both within the `(‖T₀‖, ‖∇T₀‖, ‖∇²T₀‖)` budget admitted by
  `secondCovGrad_l2NormSq_le_rawConnLap_gen`.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
curries the new tangent-direction slot as the leftmost covariant slot. All curvature is the
section-level `riemannSec`/`Tensor3rdCurv`; all the analytic packaging downstream uses the
intrinsic Riemannian fibre norm `riemannianFiberNormSq`.

## Status of the unconditional estimate

The slot-`0` matching `slot0FrameTraceMatching` is the single remaining equation; it is a
torsion-free Christoffel-bookkeeping identity between two third-order frame traces of `T₀`
(the abstract `(0, 3)` rough-Laplacian double-unfold versus the RS-level double covariant
derivative of `∇_W T₀`). It is documented as open obstruction 1 of
`CovGradRoughLapCommutatorClose2.lean`. This file proves, unconditionally, that the entire
curried curvature-defect identity follows from it.
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

/-- **Slot-`0` frame-trace matching.** For `g`, `T₀`, the point `x`, and gradient direction
`w`, the predicate
```
tensor0S_curry 2 x (Δ_∇(∇T₀) x (unit)) w
  = (∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit),
```
with `Δ_∇(∇T₀) = rawTensorConnLapSmooth g 0 3 (covGrad g 0 2 T₀)`,
`B_i := smoothOrthoFrame g x i`, and `W := smoothExtensionTangent x w`. The right-hand side
is the fixed-frame iterated-covariant trace (the left-hand side of
`frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv`). This is curvature-free; the
curvature contribution is supplied separately by the already-proved frame-trace swap. -/
def slot0FrameTraceMatching
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) : Prop :=
  tensor0S_curry (I := I) (M := M) 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w =
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

/-- **LHS reading of `Δ_∇(∇T₀)`, curried.** The unit-`(0, 0)`-evaluation of
`Δ_∇(∇T₀) = rawTensorConnLapSmooth g 0 3 (covGrad g 0 2 T₀)`, curried along the gradient
direction `w`, equals the slot-`0` curry of the abstract `(0, 3)` rough Laplacian of the
unit-evaluated gradient field, read along `W x = w`:
```
tensor0S_curry 2 x (Δ_∇(∇T₀) x (unit)) w
  = tensor0S_curry 2 x (unitGradAbstractRoughLap g T₀ x) (W x).
```
-/
lemma rawConnLap_covGrad_curry_eq_abstractRoughLap_curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      tensor0S_curry (I := I) (M := M) 2 x
        (unitGradAbstractRoughLap (I := I) (M := M) g T₀ x)
        (smoothExtensionTangent (I := I) x w x) := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  rw [rawTensorConnLap_covGrad_unit_eval_eq_abstract_roughLap (I := I) (M := M) g T₀ x]
  rw [smoothExtensionTangent_eq]

/-- **Rank-`2` `covApply` unit-evaluation intertwining.** For a smooth `Cₛ^∞`
`(0, 2)`-tensor section `σ` and a smooth tangent vector field `X`, the unit-`(0, 0)`-evaluation
of the RS-level directional derivative `covApply (tensorCov g 0 2) X σ` equals the abstract
`(0, 2)` directional derivative `covApply (tensor0SCovariantDerivative I M 2 (LeviCivita g)) X`
of the unit-evaluated section `y ↦ σ y (unit)`. This is the rank-`2` analogue of
`covApply_unit_eval_eq` (rank `3`); the unit `(0, 0)`-section is `∇`-parallel, so the two
covariant derivatives agree after the unit-evaluation. -/
lemma covApply_unit_eval_eq_two
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
        covApply (tensorCov (I := I) g 0 2) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq_two (I := I) (M := M) g σ y (X y)

/-- The directionally-derived field `∇_X T₀ = covApply (tensorCov g 0 2) X T₀` packaged as a
smooth `Cₛ^∞` `(0, 2)`-tensor section, for a smooth tangent vector field `X`. Smoothness is the
bundle-generic `covApplyRS_contMDiff` applied to the smooth section of `T₀`. -/
noncomputable def covApplyT₀Section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covApply (tensorCov (I := I) g 0 2) X (fun z => T₀.toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 2 (T := fun y => T₀.toSection y)
      T₀.toSection.contMDiff hX)

@[simp] lemma covApplyT₀Section_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyT₀Section (I := I) (M := M) g T₀ hX y =
      covApply (tensorCov (I := I) g 0 2) X (fun z => T₀.toSection z) y := rfl

/-- The twice-directionally-derived field `∇_B(∇_W T₀)` packaged as a smooth `Cₛ^∞`
`(0, 2)`-tensor section, for smooth tangent vector fields `W, B`. -/
noncomputable def covApplyBcovApplyT₀Section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {W B : Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covApply (tensorCov (I := I) g 0 2) B
      (fun z => covApply (tensorCov (I := I) g 0 2) W (fun u => T₀.toSection u) z) y)
    (covApplyRS_contMDiff (I := I) g 0 2
      (T := fun y => covApply (tensorCov (I := I) g 0 2) W (fun u => T₀.toSection u) y)
      (covApplyRS_contMDiff (I := I) g 0 2 (T := fun u => T₀.toSection u)
        T₀.toSection.contMDiff hW) hB)

/-- **Abstract `(0, 2)` form of one summand of the fixed-frame iterated trace.** The
unit-`(0, 0)`-evaluation of the RS-level iterated covariant trace summand
`∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)`, with `B_i := smoothOrthoFrame g x i` and `W` smooth, equals the
abstract `(0, 2)` covariant derivative (along `B_i`) of the once-derived abstract section
`y ↦ ∇_{Bᵢ}(∇_W T₀)(y)(unit)`:
```
∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)
  = cov₂ₐ(y ↦ ∇^{abs}_{Bᵢ}(z ↦ ∇_{W z}T₀(z)(unit)) y) x (Bᵢ x).
```
This is the two-step unit-evaluation transport (`covDeriv_unit_eval_eq_two` outer,
`covApply_unit_eval_eq_two` inner). It exhibits the slot-`0` matching's right-hand side wholly
at the abstract `(0, 2)` level — the level at which the left-hand-side reading
`curry_unitGradAbstractRoughLap_along` already lives — so the remaining matching is purely the
abstract `(0, 2)` Christoffel reorganization. -/
lemma frameTraceSummand_unit_eq_abstract
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
        (fun y : M =>
          covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i)
            (fun z : M =>
              (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                covApply (tensorCov (I := I) g 0 2)
                  (smoothExtensionTangent (I := I) x w) (fun u => T₀.toSection u) z)
                (unitZeroSec (I := I) (M := M) z)) y)
        x (smoothOrthoFrame (I := I) g x i x) := by
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hStep1 := covDeriv_unit_eval_eq_two (I := I) (M := M) g
    (covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB) x
    (smoothOrthoFrame (I := I) g x i x)
  have hInner := covApply_unit_eval_eq_two (I := I) (M := M) g
    (covApplyT₀Section (I := I) (M := M) g T₀ hW) (smoothOrthoFrame (I := I) g x i)
  calc (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x)
        (unitZeroSec (I := I) (M := M) x)
      = (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
            (fun y : M => covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB y) x
            (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              covApplyBcovApplyT₀Section (I := I) (M := M) g T₀ hW hB y)
              (unitZeroSec (I := I) (M := M) y)) x
          (smoothOrthoFrame (I := I) g x i x) := hStep1
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
              covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => covApplyT₀Section (I := I) (M := M) g T₀ hW z) y)
              (unitZeroSec (I := I) (M := M) y)) x
          (smoothOrthoFrame (I := I) g x i x) := rfl
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  covApplyT₀Section (I := I) (M := M) g T₀ hW z)
                  (unitZeroSec (I := I) (M := M) z)) y) x
          (smoothOrthoFrame (I := I) g x i x) := by rw [hInner]
    _ = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i)
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  covApply (tensorCov (I := I) g 0 2)
                    (smoothExtensionTangent (I := I) x w) (fun u => T₀.toSection u) z)
                  (unitZeroSec (I := I) (M := M) z)) y) x
          (smoothOrthoFrame (I := I) g x i x) := rfl

/-- **Curried curvature-defect identity from the slot-`0` matching.** Assume the slot-`0`
frame-trace matching `slot0FrameTraceMatching g T₀ x w`. Then the unit-`(0, 0)`-evaluation of
the canonical commutator defect `covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)`, curried
along the gradient direction `w`, equals the explicit third-order curvature contraction
`Tensor3rdCurv g 0 2 W T₀ x (unit)` (with `W := smoothExtensionTangent x w`) minus the
moving-frame residual `covGradRoughLapMovingFrameResidual g T₀ x w`:
```
tensor0S_curry 2 x (covGradRoughLapCurv g T₀ x (unit)) w
  = Tensor3rdCurv g 0 2 W T₀ x (unit) − covGradRoughLapMovingFrameResidual g T₀ x w.
```
The proof splits the defect via `SmoothCcTensor.toSection_sub`, reads the `Δ_∇(∇T₀)` term
through `rawConnLap_covGrad_curry_eq_abstractRoughLap_curry` and the matching hypothesis, reads
the `∇(Δ_∇ T₀)` term through `covGrad_rawConnLap_unit_eval_curry`, and substitutes the
frame-trace swap `frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv`. No curvature
cancellation is re-derived here — the curvature is delivered entirely by the swap. -/
theorem covGradRoughLapCurv_curry_eq_of_slot0Matching
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x)
    (hmatch : slot0FrameTraceMatching (I := I) (M := M) g T₀ x w) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        Tensor3rdCurv (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
          (fun y : M => T₀.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  have hdef : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
    rw [covGradRoughLapCurv, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
  unfold slot0FrameTraceMatching at hmatch
  rw [hmatch]
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (I := I) (M := M) g T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w] at hswap
  rw [hswap]
  abel

end Connection
end Integral
end DifferentialGeometry

end
