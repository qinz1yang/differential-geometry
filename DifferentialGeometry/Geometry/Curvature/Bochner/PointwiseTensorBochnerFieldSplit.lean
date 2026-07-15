import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TraceDiscrepancyDecomposition

/-!
# The explicit field-level genuine + bracket split of the order-`2` commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
**explicit field-level** genuine + obstruction split of the rank-generic order-`2` commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurv g s S`, a `(0, s + 1)`-tensor field; `∇S = covGrad g 0 s S`). The prior
section-field towers (`PointwiseTensorCurvL2Bound`, `OrderSeparatedCurvatureJet`) bundle the
field split together with the order-separated fibre bounds and the integrated divergence-nullity
inside a single existence-packaged primitive, leaving the explicit fields anonymous; that abstract
`∃`-field form is too weak to re-differentiate (a fibre bound does not control a covariant
gradient). This file supplies the strictly-more-primitive **explicit pointwise field identity**,
decoupled from every bound, with the genuine and obstruction fibre fields surfaced as concrete
frame sums of the on-disk curvature primitives — so the leaf-`A` node and the order-`m`
re-architecture can re-differentiate them directly.

## The explicit fields

For a `g_x`-orthonormal tangent frame `e` (the witness frame of the slot-`0` Parseval
reconstruction), with `W a := smoothExtensionTangent x (e a)` the smooth extension of the frame
direction `e a` and the genuine / bracket directional pieces
`tensor3rdCurvGenuine`, `tensor3rdCurvBracket` (`PointwiseTensorBochner`), the two fields are the
inner-product-weighted frame reconstructions of the slot-`0` curried directional split:

* `genuineThirdCurvFieldFib g s S x e w m` — the **genuine** field, the frame sum
  `∑ₐ ⟨e a, w⟩_g • tensor3rdCurvGenuine g 0 s (W a) S x (unit) m` (the `R(∇S)` and `(∇R) S`
  contractions, genuinely `rfns(∇S)` / `rfns(S)`-order);
* `bracketThirdCurvFieldFib g s S x e w m` — the **obstruction** field, the frame sum of the
  bracket directional piece `tensor3rdCurvBracket` together with the explicit moving-frame
  discrepancy `covGradRoughLapTraceDiscrepancy_gen` and residual
  `covGradRoughLapMovingFrameResidual_gen` (`TraceDiscrepancyDecomposition`,
  `CurvatureDefect`), genuinely `rfns(∇²S)`-order.

## Main result

* `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field` — the explicit field identity: in
  the slot-`0` witness frame, the section value of the defect reconstructs as the sum of the
  genuine and obstruction frame fields:
  ```
  (pointwiseTensorCurv g s S).toSection x (unit) (Fin.cons w m)
    = genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
  ```
  The genuine field carries the `R(∇S)` / `(∇R) S` curvature contractions; the obstruction field
  carries the bracket discrepancy. No anonymous subtraction is used — both fields are explicit
  frame sums of the named curvature primitives.

The proof reconstructs the unit-section of the defect from its slot-`0` curried slices through the
field-level uncurry `tensorRS_section_eq_sum_slot0Curry_uncurry` (`Slot0CurryReconstruction`), then
resolves each slot-`0` slice by the unconditional curried curvature-defect identity
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen`
(`TraceDiscrepancyDecomposition`) with `Tensor3rdCurv` split into genuine + bracket parts
(`Tensor3rdCurv_eq_genuine_add_bracket`); the discrepancy and residual obstructions are carried
explicitly into the obstruction field rather than asserted to vanish (the slot-`0` frame-trace
matching is false on a normal manifold).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace, `rawTensorConnLapSmooth`). The covariant
gradient `covGrad g 0 s` curries the new tangent-direction slot as the leftmost covariant slot. All
fibre values are read at the unit `(0, 0)`-covector through `unitZeroSec`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **`pointwiseTensorCurv` is the canonical commutator defect `covGradRoughLapCurv_gen`.** Both
are `Δ_∇(∇S) − ∇(Δ_∇ S)` by definition; the on-disk unconditional curried decomposition
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen` is phrased for the latter, so
this `rfl` bridge transports it to `pointwiseTensorCurv`. -/
lemma pointwiseTensorCurv_eq_covGradRoughLapCurv_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    pointwiseTensorCurv (I := I) (M := M) g s S =
      covGradRoughLapCurv_gen (I := I) (M := M) g s S := rfl

/-- **The slot-`0` curried slice of the defect resolves into the genuine + obstruction directional
pieces.** For a gradient direction `w`, the slot-`0` curry of the unit-evaluation of the defect
`Curv S := pointwiseTensorCurv g s S` resolves, by the unconditional curried curvature-defect
identity `covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen` and the genuine /
bracket split `Tensor3rdCurv_eq_genuine_add_bracket`, as the genuine directional piece
`tensor3rdCurvGenuine g 0 s (W w) S x (unit)` plus the obstruction piece — the bracket directional
piece `tensor3rdCurvBracket g 0 s (W w) S x (unit)`, the moving-frame discrepancy
`covGradRoughLapTraceDiscrepancy_gen`, and minus the residual
`covGradRoughLapMovingFrameResidual_gen` — where `W w := smoothExtensionTangent x w`:
```
tensor0S_curry s x (Curv S x (unit)) w
  = tensor3rdCurvGenuine g 0 s (W w) S x (unit)
    + (covGradRoughLapTraceDiscrepancy_gen g s S x w
       + tensor3rdCurvBracket g 0 s (W w) S x (unit)
       − covGradRoughLapMovingFrameResidual_gen g s S x w).
```
The discrepancy and residual are carried explicitly: the slot-`0` frame-trace matching is false on
a normal manifold, so the obstruction does not vanish; it is genuinely `∇²S`-order. -/
lemma tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
        (covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s S x w +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) -
          covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s S x w) := by
  rw [pointwiseTensorCurv_eq_covGradRoughLapCurv_gen (I := I) (M := M) g s S]
  rw [covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen
    (I := I) (M := M) g s S x w]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        Tensor3rdCurv (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [Tensor3rdCurv_eq_genuine_add_bracket (I := I) g 0 s
      (smoothExtensionTangent (I := I) x w) (fun y : M => S.toSection y) x]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  abel

/-- **The explicit genuine third-order curvature fibre field.** For a `g_x`-orthonormal frame `e`,
this is the slot-`0` frame reconstruction of the genuine directional curvature piece: the
inner-product-weighted frame sum of the model values of `tensor3rdCurvGenuine` at the smooth
extensions `W a := smoothExtensionTangent x (e a)` of the frame directions, evaluated at the unit
covector and the tail tuple `m`:
```
genuineThirdCurvFieldFib g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel (tensor3rdCurvGenuine g 0 s (W a) S x (unit)) m.
```
The summand `tensor3rdCurvGenuine g 0 s (W a) S x` carries the pure-Riemann contraction
`R(B_i, W a)(∇_{B_i} S)` and the differentiated-curvature contraction `∇_{B_i}(R(B_i, W a) S)`
(the `R(∇S)` and `(∇R) S` terms); it is genuinely `rfns(∇S)` / `rfns(S)`-order. Every summand is a
continuous function of the fibre values, so the field is re-differentiable. -/
noncomputable def genuineThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

/-- **The explicit obstruction third-order fibre field.** For a `g_x`-orthonormal frame `e`, this
is the slot-`0` frame reconstruction of the obstruction directional piece: the inner-product-
weighted frame sum of the model values of the moving-frame discrepancy
`covGradRoughLapTraceDiscrepancy_gen`, the bracket directional piece `tensor3rdCurvBracket`, and
minus the moving-frame residual `covGradRoughLapMovingFrameResidual_gen`, with `W a :=
smoothExtensionTangent x (e a)`:
```
bracketThirdCurvFieldFib g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel (covGradRoughLapTraceDiscrepancy_gen g s S x (e a)
       + tensor3rdCurvBracket g 0 s (W a) S x (unit)
       − covGradRoughLapMovingFrameResidual_gen g s S x (e a)) m.
```
This carries the frame-bracket discrepancy that the slot-`0` representation cannot remove (the
slot-`0` frame-trace matching is false on a normal manifold); after the third-order Weitzenböck
cancellation it is genuinely `rfns(∇²S)`-order. Every summand is a continuous function of the fibre
values, so the field is re-differentiable. -/
noncomputable def bracketThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      (covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s S x (e a) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s S x (e a)) m

/-- **The explicit field-level genuine + bracket split of the order-`2` commutator defect.** For a
closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, and point `x`, there is a `g_x`-orthonormal tangent frame `e` (the witness
frame of the slot-`0` Parseval reconstruction, `n = Module.finrank` directions) in which the
unit-section of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` reconstructs,
at every slot-`0` direction `w` and tail tuple `m`, as the sum of the explicit genuine and
obstruction frame fields:
```
toModel ((Curv S).toSection x (unit)) (Fin.cons w m)
  = genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m.
```

The genuine field `genuineThirdCurvFieldFib` is the inner-product-weighted frame sum of the genuine
directional curvature piece `tensor3rdCurvGenuine` (the `R(∇S)` and `(∇R) S` contractions,
genuinely `rfns(∇S)` / `rfns(S)`-order); the obstruction field `bracketThirdCurvFieldFib` is the
inner-product-weighted frame sum of the bracket directional piece `tensor3rdCurvBracket` together
with the explicit moving-frame discrepancy `covGradRoughLapTraceDiscrepancy_gen` and residual
`covGradRoughLapMovingFrameResidual_gen` (genuinely `rfns(∇²S)`-order). Both fields are explicit
frame sums of the named curvature primitives — surfaced so the leaf-`A` node and the order-`m`
re-architecture can re-differentiate them — and no anonymous subtraction is used.

The proof reconstructs the unit-section of `Curv S` from its slot-`0` curried slices through the
field-level uncurry `tensor0S_eq_sum_slot0_uncurry` (`Slot0CurryReconstruction`), then resolves each
slot-`0` slice by `tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction` (the unconditional
curried curvature-defect identity with `Tensor3rdCurv` split into genuine + bracket) and splits the
resulting frame sum by additivity of the model coercion. The discrepancy and residual are carried
explicitly into the obstruction field rather than asserted to vanish — the slot-`0` frame-trace
matching is false on a normal manifold, so the obstruction is genuinely nonzero. -/
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hrecon⟩ :=
    tensor0S_eq_sum_slot0_uncurry (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  rw [hrecon
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

end Connection
end Integral
end DifferentialGeometry
