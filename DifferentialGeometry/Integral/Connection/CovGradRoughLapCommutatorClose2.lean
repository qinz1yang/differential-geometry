import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorDoubleUnfold
import DifferentialGeometry.Integral.Connection.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Integral.Connection.CurvatureBundling

/-!
# Closing the `(0, 2) → (0, 3)` rough-Laplacian / covariant-gradient commutator:
the slot-`0` free-direction reduction

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, this file
takes the abstract `(0, 3)` reduction of the order-`2` Gårding commutator from
`CovGradRoughLapCommutator{,Abstract,Assembly,DoubleUnfold}.lean` and reduces the
remaining curvature reconciliation to a single explicit equation read along a
**free gradient direction** `w`, using the right-hand-side frame-trace third-order
Weitzenböck swap `frame_trace_thirdCovDeriv_swap` of `TensorThirdOrderWeitzenbock.lean`.

## The reduction to a single covariant slot

Both sides of the target commutator
```
Δ_∇(∇T₀) (x) = ∇(Δ_∇ T₀) (x) + Curv x
```
are `(0, 3)`-tensors. By unit-extensionality (`tensor03_ext_unit`) it suffices to
compare their unit `(0, 0)`-evaluations, which are elements of `Tensor0SSpace 3 I x`.
Two `(0, 3)`-tensors are equal iff their slot-`0` curryings `tensor0S_curry 2 x · w`
agree as continuous linear maps, i.e. for every tangent direction `w` — the
gradient slot is read along `w`. We extend `w` to a smooth field
`W := smoothExtensionTangent x w` so that the directional covariant-derivative
machinery applies.

## What this file establishes (the genuinely-proven content)

* `curry_unitGradAbstractRoughLap_along` — the **left-hand-side reading**: the
  slot-`0` curry of the abstract `(0, 3)` rough Laplacian of `U := unitGradField g
  T₀` along the extended gradient direction `W = smoothExtensionTangent x w` is the
  frame sum of the depth-`2` and depth-`1` slot-`0` unfolds of each summand (via the
  committed double-unfold lemmas `curry_abstract_covDeriv_covApply_unitGrad_unfold`
  and `curry_abstract_covDeriv_unitGrad_unfold'`).

* `covGrad_rawConnLap_unit_eval_curry` — the **right-hand-side reading**: the
  slot-`0` curry of the unit-evaluation of the gradient `covGrad g 0 2 (Δ_∇ T₀)`
  along `w` is the directional covariant derivative of `Δ_∇ T₀ = rawTensorConnLapSmooth
  g 0 2 T₀`, read at the unit `(0, 0)`-tensor:
  `tensor0S_curry 2 x (∇(Δ_∇T₀) x (unit)) w = (∇_w Δ_∇T₀)(x)(unit)`.

* `rawConnLapSection_eq_frame_trace_secondCovDeriv_section` — the section-level
  K1b identity: the underlying section of `Δ_∇ T₀` agrees pointwise with the
  frame trace `∑ᵢ ∇²_{Bᵢ, Bᵢ} T₀`.

* `frame_trace_third_eq_swap_unit` — the RHS frame-trace swap wired through the
  unit: with `W = smoothExtensionTangent x w`,
  ```
  (∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit)
    = (∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀)(x)(unit) + Tensor3rdCurv g 0 2 W T₀ x (unit).
  ```
  This is `frame_trace_thirdCovDeriv_swap` at rank `(0, 2)`, evaluated at the unit
  `(0, 0)`-tensor.

* `covDeriv_unit_eval_eq_two` — the `s = 2` unit-evaluation intertwining: the
  unit-read of an RS-level `(0, 2)`-rank directional covariant derivative equals the
  abstract `(0, 2)` covariant derivative of the unit-read section. This is the
  transport returning the abstract `(0, 2)` slot-`0` unfolds of
  `curry_unitGradAbstractRoughLap_along` to the RS level consumed by the swap.

## The precise remaining gap (documented, not assumed)

Closing the full commutator chains `curry_unitGradAbstractRoughLap_along` (LHS) to
`covGrad_rawConnLap_unit_eval_curry` + `frame_trace_third_eq_swap_unit` (RHS). Two
genuinely-distinct obstructions remain, both at the slot-`0` frame-Christoffel level:

1. **Slot-`0` Christoffel family matching.** The LHS reading carries, per frame
   summand, the slot-`0` Christoffel corrections `(∇^{TM}_{Bᵢ} W)`, `(∇^{TM}_W Bᵢ)`
   (from the depth-`2` and depth-`1` unfolds), whereas the RS-level frame trace
   `∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)` differentiates the FIXED direction-`W` covariant
   derivative `∇_W T₀`. After transporting the abstract `(0, 2)` unfolds to the RS
   level by `covDeriv_unit_eval_eq_two`, the difference is the Christoffel /
   bracket family `(∇_{(∇^{TM}_{Bᵢ} W)(·)} T₀)(·)(unit)`; matching it against the
   bracket terms of `Tensor3rdCurv` (`∇_{[Bᵢ, W]}(∇_{Bᵢ} T₀)` etc.) via
   torsion-freeness `(∇^{TM}_{Bᵢ} W) − (∇^{TM}_W Bᵢ) = [Bᵢ, W]` is the first piece.

2. **Moving-frame vs fixed-frame residual.** The swap's right-hand side
   `∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀ (x)` differentiates the FIXED-at-`x` frame field
   `Bᵢ := smoothOrthoFrame g x i` along `W`, whereas `∇_W(Δ_∇T₀)(x) =
   (∇_w Δ_∇T₀)(x)` (the `covGrad_rawConnLap_unit_eval_curry` reading)
   differentiates the rough Laplacian section `z ↦ ∑ᵢ ∇²_{C^z_i, C^z_i} T₀(z)` with
   the MOVING `g_z`-orthonormal frame `C^z_i := smoothOrthoFrame g z i`. Because
   `Bᵢ(z) = smoothOrthoFrame g x i (z)` is `g_z`-orthonormal only at `z = x` (the
   metric varies), the fixed-frame second-derivative section and the moving-frame
   rough-Laplacian section agree at `x` but differ in a neighbourhood, so their
   `W`-derivatives differ by an explicit frame-derivative correction. Frame
   invariance of the rough Laplacian (`rawTensorConnLap_eq_frame_trace`) governs the
   pointwise value but not the `W`-derivative; the residual correction must be folded
   into the curvature field. This second obstruction is the reason a literal
   `Curv = Tensor3rdCurv` is not directly the commutator defect — the bundled `Curv`
   must additionally absorb the moving-frame derivative correction.

Neither obstruction is assumed here; the file provides the verified both-sides
reductions of the commutator to a single explicit slot-`0` frame-Christoffel
equation, leaving the matching (1) and the moving-frame residual (2) as the
remaining work.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (the frame trace), matching
`CovGradRoughLapCommutatorAbstract.lean` and `TensorThirdOrderWeitzenbock.lean`. The
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

/-- **Right-hand-side reading.** The slot-`0` curry of the unit-evaluation of the
gradient `covGrad g 0 2 (Δ_∇ T₀)` along a tangent direction `w` is the directional
covariant derivative of `Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀`, evaluated at the
unit `(0, 0)`-tensor:
```
tensor0S_curry 2 x (∇(Δ_∇T₀) x (unit)) w = (∇_w Δ_∇T₀)(x)(unit).
```
-/
lemma covGrad_rawConnLap_unit_eval_curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth g 0 2 T₀) x w)
        (unitZeroSec (I := I) (M := M) x) := by
  have := curry_covGrad_unit_eval (I := I) (M := M) g
    (rawTensorConnLapSmooth g 0 2 T₀) x w
  exact this

/-- **Section-level K1b for the rank-`2` rough Laplacian.** The underlying section of
`Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀`, evaluated at `x`, is the frame trace
`∑ᵢ ∇²_{Bᵢ, Bᵢ} T₀ (x)` over the smooth `g_x`-orthonormal frame. -/
lemma rawConnLapSection_eq_frame_trace_secondCovDeriv_section
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth g 0 2 T₀).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 2
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => T₀.toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 2
    (fun y : M => T₀.toSection y) x

/-- **Frame-trace swap, unit-read.** For the smooth field `W := smoothExtensionTangent
x w`, the unit-`(0, 0)`-evaluation of the rank-`(0, 2)` frame-trace third covariant
derivative `∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)` equals the unit-evaluation of the swapped frame
trace `∑ᵢ ∇_W ∇_{Bᵢ}∇_{Bᵢ} T₀` plus the unit-read curvature defect `Tensor3rdCurv g
0 2 W T₀ x`. This is `frame_trace_thirdCovDeriv_swap` (rank `(0, 2)`) applied to the
unit `(0, 0)`-tensor. -/
lemma frame_trace_third_eq_swap_unit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          Tensor3rdCurv (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hT₀ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) b (T₀.toSection b)) :=
    T₀.toSection.contMDiff
  have hswap := frame_trace_thirdCovDeriv_swap (I := I) g 0 2
    (W := smoothExtensionTangent (I := I) x w) (T := fun y : M => T₀.toSection y) (x := x)
    hW hT₀
  have happ := congrArg
    (fun (φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) =>
      φ (unitZeroSec (I := I) (M := M) x)) hswap
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply] using happ

/-- **Left-hand-side reading.** The slot-`0` curry of the abstract `(0, 3)` rough
Laplacian of `U := unitGradField g T₀` along the extended gradient direction
`W := smoothExtensionTangent x w` is the frame sum of the depth-`2` and depth-`1`
slot-`0` unfolds. With `B_i := smoothOrthoFrame g x i`, `W := smoothExtensionTangent x w`,
and `C_i := smoothExtensionTangent x ((∇_{B_i} B_i)(x))`, it equals
```
∑ᵢ [ cov₂ₐ.toFun (z ↦ cov₂ₐ.toFun (u ↦ (∇_{W u} T₀)(u)(unit)) z (Bᵢ z)
                   − (∇_{(∇^{TM}_{Bᵢ} W)(z)} T₀)(z)(unit)) x (Bᵢ x)
     − curriedSection (covApply cov₃ₐ Bᵢ U) x ((∇^{TM}_{Bᵢ} W)(x))
     − ( cov₂ₐ.toFun (z ↦ (∇_{W z} T₀)(z)(unit)) x (Cᵢ x)
         − (∇_{(∇^{TM}_{Cᵢ} W)(x)} T₀)(x)(unit) ) ].
```
This is the slot-`0` distribution of the abstract rough Laplacian, with each summand
read by the committed double-unfold lemmas. -/
lemma curry_unitGradAbstractRoughLap_along
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        (unitGradAbstractRoughLap (I := I) (M := M) g T₀ x)
        (smoothExtensionTangent (I := I) x w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        ( ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                curriedSection I M
                  (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                    (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                    (unitGradField (I := I) (M := M) g T₀)) z
                  (smoothExtensionTangent (I := I) x w z)) x
              (smoothOrthoFrame (I := I) g x i x) -
            curriedSection I M
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3
                (LeviCivita (I := I) g)) (smoothOrthoFrame (I := I) g x i)
                (unitGradField (I := I) (M := M) g T₀)) x
              ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                (smoothOrthoFrame (I := I) g x i x))) -
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)).toFun
              (fun z : M =>
                (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace 2 I z from
                  tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ z
                    (smoothExtensionTangent (I := I) x w z))
                  (unitZeroSec (I := I) (M := M) z)) x
              (smoothExtensionTangent (I := I) x
                ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x)) x) -
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ x
                ((LeviCivita (I := I) g).toFun (smoothExtensionTangent (I := I) x w) x
                  (smoothExtensionTangent (I := I) x
                    ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
                      (smoothOrthoFrame (I := I) g x i x)) x)))
              (unitZeroSec (I := I) (M := M) x))) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  rw [unitGradAbstractRoughLap_def]
  rw [show (tensor0S_curry (I := I) (M := M) 2 x
        (∑ i : Fin (Module.finrank ℝ E),
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x))))) =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensor0S_curry (I := I) (M := M) 2 x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g x i) (unitGradField (I := I) (M := M) g T₀)) x
              (smoothOrthoFrame (I := I) g x i x) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
              (unitGradField (I := I) (M := M) g T₀) x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x)))) from
      map_sum (tensor0S_curry (I := I) (M := M) 2 x) _ _]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothExtensionTangent (I := I) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))) :=
    smoothExtensionTangent_contMDiff x _
  rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [curry_abstract_covDeriv_covApply_unitGrad_unfold (I := I) (M := M) g T₀ hB hB hW]
  have hCx : smoothExtensionTangent (I := I) x
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) x =
      (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x) :=
    smoothExtensionTangent_eq x _
  rw [show
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
        (unitGradField (I := I) (M := M) g T₀) x
        (smoothExtensionTangent (I := I) x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x)) x) from by rw [hCx]]
  rw [curry_abstract_covDeriv_unitGrad_unfold' (I := I) (M := M) g T₀ hC hW]

/-- **Unit-evaluation commutes with the rank-`(0, 2)` covariant derivative.** For a
smooth `Cₛ^∞` `(r = 0, 2)`-tensor section `σ` and tangent vector `v`, the directional
RS-level covariant derivative of `σ`, applied to the unit `(0, 0)`-tensor, equals the
abstract `(0, 2)`-tensor covariant derivative of the unit-evaluated section
`y ↦ σ y (unit)`:
```
(∇^{(0,2)RS}_v σ)(x)(unit) = (∇^{(0,2)abs}_v (y ↦ σ y (unit)))(x).
```
This is `tensorRSCovariantDerivative_zeroS_unit_eval` at `s = 2`; it is the transport
turning the abstract `(0, 2)` slot-`0` unfolds of
`curry_unitGradAbstractRoughLap_along` into RS-level directional covariant derivatives
(the form consumed by `frame_trace_thirdCovDeriv_swap`). -/
lemma covDeriv_unit_eval_eq_two
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v :=
  tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g 2 σ x v

end Connection
end Integral
end DifferentialGeometry

end
