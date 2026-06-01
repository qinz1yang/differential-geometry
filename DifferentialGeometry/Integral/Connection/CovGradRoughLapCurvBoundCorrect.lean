import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvRicciRoute

/-!
# The corrected curried curvature-defect identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` Gårding
commutator defect is
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)   (a `(0, 3)`-tensor field),
```
(`CovGradRoughLapCommutatorClose3.lean`). The headline of this file is the **unconditional**
curried decomposition of that defect along a tangent direction `w`, read at the unit
`(0, 0)`-tensor:
```
tensor0S_curry 2 x (covGradRoughLapCurv g T₀ x (unit)) w
  = covGradRoughLapTraceDiscrepancy g T₀ x w
    + Tensor3rdCurv g 0 2 (smoothExtensionTangent x w) T₀ x (unit)
    − covGradRoughLapMovingFrameResidual g T₀ x w.
```

## Why the slot-`0` matching route is unavailable

The slot-`0` frame-trace matching predicate `slot0FrameTraceMatching`
(`CovGradRoughLapCurvRicciRoute.lean`) asserts that the curried unit-evaluation of
`Δ_∇(∇T₀)` equals the **bare** fixed-frame iterated trace `∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)`.
That equality is false: the rough Laplacian `Δ_∇ = rawTensorConnLap` carries, by definition,
the Christoffel correction `−∑ᵢ ∇_{(∇_{Bᵢ}Bᵢ)}(·)` (and the bare iterated trace also
differentiates the fixed extension `W`), so the curried unit-evaluation of `Δ_∇(∇T₀)` and the
bare iterated trace genuinely differ. Their difference is recorded here as the explicit,
second-covariant-derivative-order field `covGradRoughLapTraceDiscrepancy`. The headline
decomposition is **unconditional** — no matching predicate is assumed; the discrepancy is
carried as a named term rather than asserted to vanish.

## What this file establishes

* `covGradRoughLapTraceDiscrepancy` — the **frame-trace discrepancy**: the `(0, 2)`-tensor
  difference of the curried unit-evaluation of `Δ_∇(∇T₀)` and the bare fixed-frame iterated
  trace `∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)`. It collects the Christoffel correction of the
  rough Laplacian together with the bare trace's differentiation of the fixed extension `W`;
  both contributions are second-covariant-derivative-order in `T₀`.

* `covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual` — the **headline
  unconditional curried identity**: the curried unit-evaluation of the canonical defect equals
  the discrepancy plus the explicit curvature field `Tensor3rdCurv` minus the moving-frame
  residual. The proof is pure algebra from the proved frame-trace swap
  `frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv`
  (`CovGradRoughLapCommutatorClose3.lean`) and the definition of `covGradRoughLapCurv`; no
  curvature cancellation is re-derived (the curvature is delivered entirely by the swap).

## The precise remaining gap to the unconditional Gårding estimate (documented, not assumed)

The hypothesis `hpt` of `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
(`CovGradRoughLapCurvL2Bound.lean`) is the **(0, 3)** pointwise fibre-norm bound
```
riemannianFiberNormSq g 0 3 x (covGradRoughLapCurv g T₀).toSection x
  ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x).
```
The headline identity here is the **slot-`0`-curried (0, 2)** decomposition of that defect.
Reducing the (0, 3) fibre norm to a frame sum of curried (0, 2) fibre norms requires a
slot-split Parseval bridge `riemannianFiberNormSq g 0 3 x T = ∑ₐ riemannianFiberNormSq g 0 2 x
(tensor0S_curry 2 x (T unit) eₐ)` over a `g_x`-orthonormal tangent frame — not yet built.
With that bridge in hand, the three curried summands must each be controlled within the
`(rfns T₀, rfns ∇T₀, rfns ∇²T₀)` budget:

1. `covGradRoughLapTraceDiscrepancy` — the Christoffel + extension-derivative correction,
   bounded by `rfns(∇T₀)` and `rfns(∇²T₀)` (the smooth frame data `∇_{Bᵢ}Bᵢ`, `∇_{Bᵢ}W` are
   bounded on the compact `M`). This is the genuine new analytic content.
2. `Tensor3rdCurv g 0 2 W T₀ x (unit)` — the four curvature/bracket contractions, bounded by
   `rfns(T₀)`, `rfns(∇T₀)`, `rfns(∇²T₀)` via the curvature Parseval lemmas
   (`RiemannianFiberNormSqRiemannOpHigherRankParseval.lean`,
   `Tensor3rdCurvFiberNormBound.lean`).
3. `covGradRoughLapMovingFrameResidual g T₀ x w` — the moving-vs-fixed frame correction,
   bounded by `rfns(∇²T₀)` (`CovGradRoughLapCommutatorClose3.lean`).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0
s` curries the new tangent-direction slot as the leftmost covariant slot. All fibre norms are
the intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
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

/-- **The frame-trace discrepancy.** With `Δ_∇(∇T₀) = rawTensorConnLapSmooth g 0 3
(covGrad g 0 2 T₀)`, `B_i := smoothOrthoFrame g x i`, and `W := smoothExtensionTangent x w`,
the `(0, 2)`-tensor difference of the curried unit-evaluation of `Δ_∇(∇T₀)` and the bare
fixed-frame iterated trace:
```
covGradRoughLapTraceDiscrepancy g T₀ x w
  := tensor0S_curry 2 x (Δ_∇(∇T₀) x (unit)) w
       − (∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀))(x)(unit).
```
It collects the rough-Laplacian Christoffel correction together with the bare iterated trace's
differentiation of the fixed extension `W`; both contributions are
second-covariant-derivative-order in `T₀`. -/
noncomputable def covGradRoughLapTraceDiscrepancy
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  tensor0S_curry (I := I) (M := M) 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w -
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

/-- Defining identity for `covGradRoughLapTraceDiscrepancy`. -/
lemma covGradRoughLapTraceDiscrepancy_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w =
      tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (rawTensorConnLapSmooth (I := I) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g 0 2).toFun
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g 0 2)
                  (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
              (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl

/-- **Headline: the unconditional curried curvature-defect identity.** The curried
unit-`(0, 0)`-evaluation of the canonical commutator defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)`, along the gradient direction `w`, equals the
frame-trace discrepancy plus the explicit curvature field `Tensor3rdCurv g 0 2 W T₀ x (unit)`
(with `W := smoothExtensionTangent x w`) minus the moving-frame residual
`covGradRoughLapMovingFrameResidual g T₀ x w`:
```
tensor0S_curry 2 x (covGradRoughLapCurv g T₀ x (unit)) w
  = covGradRoughLapTraceDiscrepancy g T₀ x w
    + Tensor3rdCurv g 0 2 W T₀ x (unit)
    − covGradRoughLapMovingFrameResidual g T₀ x w.
```
The proof splits the defect via `SmoothCcTensor.toSection_sub`, leaves the `Δ_∇(∇T₀)` term as
the curried unit-evaluation, reads the `∇(Δ_∇ T₀)` term through
`covGrad_rawConnLap_unit_eval_curry`, substitutes the frame-trace swap
`frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv`, and recombines with the
definition of the discrepancy by `abel`. It is **unconditional** — no slot-`0` matching is
assumed. -/
theorem covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w +
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
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (I := I) (M := M) g T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w] at hswap
  rw [covGradRoughLapTraceDiscrepancy_def (I := I) (M := M) g T₀ x w]
  rw [hswap]
  abel

end Connection
end Integral
end DifferentialGeometry

end
