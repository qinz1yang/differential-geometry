import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSplitParsevalBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality

/-!
# Bare-curry form of the slot-`0` Parseval decomposition of the `(0, s+1)`-tensor fibre norm

The on-disk slot-`0` Parseval decomposition `riemannianFiberNormSq_succ_eq_sum_slot0Curry`
(`SlotSplitParsevalBridge.lean`) reads the intrinsic Riemannian fibre norm squared of a
`(0, s+1)` covariant tensor `T` at a point `x` as the frame-sum, over a `g`-orthonormal tangent
frame `e`, of the slot-`s` fibre norms of the *wrapper* slot-`0` curries
`slot0Curry g x s e K₀ T a`. The third-order Gårding/Weitzenböck consumers
(`TraceDiscrepancyDecomposition.lean`, `Order2Defect/SlotSplitBound.lean`,
`Connection/Laplacian/RoughLaplacianSecondCovGradL2Bound.lean`) want the same decomposition
phrased with the **bare** tensor curry of the unit-section, i.e.
```
riemannianFiberNormSq g 0 (s+1) x T
  = ∑ a, riemannianFiberNormSq g 0 s x (tensor0SAsRS x (tensor0S_curry s x (T (unit)) (e a)))
```
where `T (unit)` is `(T : CLM)` evaluated at the unit `(0, 0)`-tensor `unitZeroSec x`, and
`tensor0SAsRS x C` re-packages a model `(0, s)`-tensor `C` as a `TensorRSSpace 0 s I x` (exactly
the wrapper `slot0Curry` uses internally). This is the documented "slot-split Parseval bridge"
recorded in `TraceDiscrepancyDecomposition.lean` (the `s = 2` / rank-`3` case) as the precise
reduction `rfns g 0 3 x T = ∑ₐ rfns g 0 2 x (tensor0S_curry 2 x (T unit) eₐ)`.

The content is pure fibre linear algebra over the proved Parseval split: the bare curry of the
unit-section, wrapped by `tensor0SAsRS`, is **definitionally** the on-disk `slot0Curry` wrapper
(`slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec`), because the empty-index coframe covector
`coframeS g x 0 e K₀` coincides with the unit `(0, 0)`-tensor `unitZeroSec x`
(`coframeS_zero_eq_unitZeroSec`).

## Main definitions

* `tensor0SAsRS` — the canonical `(0, s)`-tensor wrapper of a model `(0, s)`-tensor (scale by the
  unit scalar extracted from the `(0, 0)` argument), matching the internal wrapper of `slot0Curry`.

## Main results

* `tensor0SAsRS_apply` — the defining evaluation formula for `tensor0SAsRS`.
* `coframeS_zero_eq_unitZeroSec` — the empty-index coframe covector equals the unit
  `(0, 0)`-tensor `unitZeroSec x`.
* `slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec` — the on-disk `slot0Curry` wrapper equals the
  `tensor0SAsRS`-wrapped bare curry of the unit-section.
* `riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry` — the bare-curry slot-`0` Parseval split.
* `riemannianFiberNormSq_three_eq_sum_bareSlot0Curry` — the `s = 2` / rank-`3` specialization
  consumed by the third-order Gårding estimate.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The canonical `(0, s)`-tensor wrapper of a model `(0, s)`-tensor `C`: the continuous linear
map `τ ↦ (tensor00Scalar x τ) • C` extracting the unit scalar from the `(0, 0)` argument and
scaling `C`. This is exactly the wrapper used internally by `slot0Curry`. -/
noncomputable def tensor0SAsRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight C

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of `tensor0SAsRS`.** `(tensor0SAsRS x C) τ = (tensor00Scalar x τ) • C`. -/
lemma tensor0SAsRS_apply {s : ℕ} (x : M) (C : Tensor0SSpace s I x)
    (τ : Tensor0SSpace 0 I x) :
    (tensor0SAsRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • C := by
  change ((tensor00Scalar (I := I) (M := M) x).smulRight C) τ = _
  rw [ContinuousLinearMap.smulRight_apply]

set_option linter.unusedSectionVars false in
/-- **The empty-index coframe covector is the unit `(0, 0)`-tensor.** The rank-`0` coframe
covector `coframeS g x 0 e K₀` (an empty product, scalar value `1`) coincides with the constant
unit `(0, 0)`-tensor `unitZeroSec x`. -/
lemma coframeS_zero_eq_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) :
    coframeS (I := I) (M := M) g x 0 e K₀ = unitZeroSec (I := I) (M := M) x := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
  intro u
  rw [coframeS_apply (I := I) (M := M) g x 0 e K₀ u]
  rw [Fin.prod_univ_zero]
  rw [show ((unitZeroSec (I := I) (M := M) x) u : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) u from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

set_option linter.unusedSectionVars false in
/-- **The on-disk `slot0Curry` wrapper is the `tensor0SAsRS`-wrapped bare curry of the
unit-section.** For a `g`-orthonormal frame `e`,
`slot0Curry g x s e K₀ T a = tensor0SAsRS x (tensor0S_curry s x ((T) (unitZeroSec x)) (e a))`.
The proof unfolds both wrappers and identifies the empty-index coframe covector with
`unitZeroSec x` via `coframeS_zero_eq_unitZeroSec`. -/
lemma slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SAsRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) := by
  unfold slot0Curry tensor0SAsRS
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]

/-- **Bare-curry slot-`0` Parseval decomposition of the `(0, s+1)`-tensor fibre norm.** There is
a `g`-orthonormal tangent frame `e` (with `n = Module.finrank` directions) in which the intrinsic
`(0, s+1)` fibre norm squared of `T` at `x` is the frame-sum, over the slot-`0` direction, of the
slot-`s` fibre norms of the `tensor0SAsRS`-wrapped bare curries of the unit-section
`(T) (unitZeroSec x)`:
```
riemannianFiberNormSq g 0 (s+1) x T
  = ∑ a, riemannianFiberNormSq g 0 s x (tensor0SAsRS x (tensor0S_curry s x (T (unit)) (e a))).
```
This is `riemannianFiberNormSq_succ_eq_sum_slot0Curry` rephrased through the bare-curry bridge
`slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec`; it is the documented "slot-split Parseval bridge"
the third-order Gårding/Weitzenböck consumers reduce the `(0, 3)` fibre norm against. -/
theorem riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SAsRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) s x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) := by
  classical
  obtain ⟨n, e, K₀, hn, hsplit⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, hn, ?_⟩
  rw [hsplit]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ T a]

/-- **Bare-curry slot-`0` Parseval, rank-`3` (`s = 2`).** The `s = 2` specialization of
`riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry`: the exact reduction of the `(0, 3)` fibre norm
into a frame-sum of curried `(0, 2)` fibre norms documented in `TraceDiscrepancyDecomposition.lean`
as the remaining slot-split bridge for the third-order Gårding estimate. Apply with
`T := (covGradRoughLapCurv g T₀).toSection x` to reduce the `(0, 3)` `hpt` of
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound` to per-frame-direction `(0, 2)`
curried bounds on the curried curvature-defect. -/
theorem riemannianFiberNormSq_three_eq_sum_bareSlot0Curry
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TensorRSSpace 0 3 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (tensor0SAsRS (I := I) (M := M) x
              (tensor0S_curry (I := I) (M := M) 2 x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) :=
  riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry (I := I) (M := M) g 2 x T

end Connection
end Integral
end DifferentialGeometry

end
