import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvBoundCorrect
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound
import DifferentialGeometry.Integral.Connection.SlotSplitParsevalBridge

/-!
# Slot-split tensorial reduction of the order-`2` curvature-defect fibre-norm bound

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the order-`2` covariant Gårding
estimate consumes the **pointwise** fibre-norm bound on the canonical commutator defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` (a `(0, 3)`-tensor field):
```
riemannianFiberNormSq g 0 3 x (covGradRoughLapCurv g T₀).toSection x
  ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x).
```
(`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`,
`CovGradRoughLapCurvL2Bound.lean`).

This file works **directly** with the `(0, 3)`-tensor `covGradRoughLapCurv g T₀` and its
fibre components, with **no** vector-field currying and **no** reliance on the (uncontrolled)
`smoothExtensionTangent`. The route is the slot-`0` Parseval decomposition
(`riemannianFiberNormSq_succ_eq_sum_slot0Curry`, `SlotSplitParsevalBridge.lean`), which splits
the `(0, 3)` fibre norm into a finite frame-sum of slot-`0` curried `(0, 2)` fibre norms — the
exact fixed-orthonormal-frame components the third-order Weitzenböck content lives in.

## What is established (unconditionally)

* `riemannianFiberNormSq_three_eq_sum_slot0Curry` — the bare slot-`0` Parseval split for the
  defect at rank `(0, 3)`: a `∃`-packaged orthonormal frame `e` with
  `rfns g 0 3 x (defect) = ∑ a, rfns g 0 2 x (slot0Curry … defect a)`.

* `riemannianFiberNormSq_three_le_of_slot0_bound` — the **slot-split reduction**: if each
  slot-`0` curried `(0, 2)` fibre norm of the defect is bounded by a single common nonnegative
  bound `B`, then the `(0, 3)` fibre norm is bounded by `n · B` where `n = finrank ℝ E`. This is
  the genuine bridge from a per-frame-direction `(0, 2)` curried bound to the `(0, 3)` `hpt`
  shape.

* `riemannianFiberNormSq_three_budget_of_slot0_budget` — the same reduction packaged in the
  `hpt` budget shape: a per-direction bound by `D₀² · budget` lifts to a `(n · D₀²)`-multiple
  of the budget. Combined with `Real.sqrt` this exposes the `C₀ = √n · D₀` constant of the
  `(0, 3)` `hpt`.

## The precise remaining mathematical content (documented, not assumed)

The slot-split reduces `hpt` to the per-frame-direction `(0, 2)` curried bound
```
∀ a, rfns g 0 2 x (slot0Curry g x 2 e K₀ (covGradRoughLapCurv g T₀).toSection x a)
       ≤ D₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x).
```
By the headline unconditional curried identity
`covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual`
(`CovGradRoughLapCurvBoundCorrect.lean`), the curried `(0, 2)` value along a direction `w`
decomposes as
```
discrepancy(w) + Tensor3rdCurv(W, T₀)(unit) − residual(w),
```
with `W := smoothExtensionTangent x w`. **Each of these three terms is individually
third-covariant-derivative-order in `T₀` and depends on the (uncontrolled) first jet of `W`
through the Lie brackets `[Bᵢ, W]`; only their sum (the genuine `(0, 3)`-tensor defect, which is
tensorial in `w`) is `∇²`-and-curvature order.** Consequently a per-term fibre bound through
`smoothExtensionTangent` is *false* (this was the failure mode of the two earlier attempts on
this target). The honest closure requires the third-order Weitzenböck cancellation: the `∇³T₀`
and `[Bᵢ, W]`-jet contributions of the discrepancy, the residual, and the bracket summands of
`Tensor3rdCurv` cancel, leaving a tensorial `∇²`-and-curvature remainder. That cancellation is
not performed in the available infrastructure and is the precise remaining subgoal.

## Conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0
s` raises the tensor rank from `(0, s)` to `(0, s + 1)`, currying the new tangent-direction slot
as the leftmost covariant slot. All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq` — never a model-space norm or chart operator norm, which are genuinely
unbounded on multi-chart manifolds.
-/

noncomputable section

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
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

set_option linter.unusedSectionVars false in
/-- **Slot-`0` Parseval split of the canonical curvature defect.** For the canonical commutator
defect `covGradRoughLapCurv g T₀` (a `(0, 3)`-tensor field), the intrinsic `(0, 3)` fibre norm
at `x` of its underlying section value decomposes over an (internally-built) `g`-orthonormal
tangent frame `e` into the frame-sum of the slot-`s` fibre norms of the slot-`0` curries:
```
riemannianFiberNormSq g 0 3 x (covGradRoughLapCurv g T₀).toSection x
  = ∑ a, riemannianFiberNormSq g 0 2 x
      (slot0Curry g x 2 e K₀ (covGradRoughLapCurv g T₀).toSection x a).
```
This is `riemannianFiberNormSq_succ_eq_sum_slot0Curry` with `s = 2` and
`T := (covGradRoughLapCurv g T₀).toSection x`. -/
theorem riemannianFiberNormSq_three_eq_sum_slot0Curry
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (slot0Curry (I := I) (M := M) g x 2 e K₀
              ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) := by
  exact riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g 2 x
    ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)

set_option linter.unusedSectionVars false in
/-- **Slot-split reduction (raw bound form).** If for some `g`-orthonormal frame `e` realising
the Parseval split, each slot-`0` curried `(0, 2)` fibre norm of the canonical defect at `x` is
bounded by a common nonnegative bound `B`, then the `(0, 3)` fibre norm of the defect at `x` is
bounded by `n · B`. The hypothesis is over the *same* frame `e` that the Parseval split
produces; the conclusion is the `(0, 3)` fibre-norm bound. -/
theorem riemannianFiberNormSq_three_le_of_slot0_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hsplit : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
      ∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a))
    (B : ℝ)
    (hbound : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤ (n : ℝ) * B := by
  classical
  rw [hsplit]
  calc
    (∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (slot0Curry (I := I) (M := M) g x 2 e K₀
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a))
        ≤ ∑ _a : Fin n, B := Finset.sum_le_sum (fun a _ => hbound a)
    _ = (n : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The rfns budget at `x`: `rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀)`, the exact right-hand-side
combination of `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`. -/
private noncomputable def rfnsBudget
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) : ℝ :=
  riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
    riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
      ((covGrad (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)

set_option linter.unusedSectionVars false in
private lemma rfnsBudget_nonneg
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    0 ≤ rfnsBudget (I := I) (M := M) g T₀ x := by
  unfold rfnsBudget
  have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x (T₀.toSection x)
  have h2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x
    ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)
  have h3 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (3 + 1) x
    ((covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
  linarith

set_option linter.unusedSectionVars false in
/-- **The `hpt` packaging from the per-direction budget bound.** Suppose that, for every
`x`, there is a `g`-orthonormal Parseval frame `e` at `x` (with `n = finrank ℝ E` directions)
realising the slot-`0` split such that each slot-`0` curried `(0, 2)` fibre norm of the canonical
defect is bounded by `D₀²` times the rfns budget at `x`. Then the canonical defect satisfies the
exact `(0, 3)` `hpt` of `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`, with
`C₀ = √(finrank ℝ E) · D₀` (so `C₀² = (finrank ℝ E) · D₀²`).

The per-frame hypothesis is the genuine remaining analytic input: it is the per-direction
`(0, 2)` curried bound, *not* the `(0, 3)` conclusion. The lift to the `(0, 3)` `hpt` is the
slot-split reduction `riemannianFiberNormSq_three_le_of_slot0_bound`. -/
theorem covGradRoughLapCurv_hpt_of_slot0_budget
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (D₀ : ℝ)
    (hbudget : ∀ x : M,
      ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
        n = Module.finrank ℝ (TangentSpace I x) ∧
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) =
          (∑ a : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (slot0Curry (I := I) (M := M) g x 2 e K₀
                ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a)) ∧
        ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (slot0Curry (I := I) (M := M) g x 2 e K₀
                ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) a) ≤
            D₀ ^ 2 * rfnsBudget (I := I) (M := M) g T₀ x) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        (Real.sqrt (Module.finrank ℝ E) * D₀) ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := by
  classical
  intro x
  obtain ⟨n, e, K₀, hn, hsplit, hper⟩ := hbudget x
  have hle : riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        (n : ℝ) * (D₀ ^ 2 * rfnsBudget (I := I) (M := M) g T₀ x) :=
    riemannianFiberNormSq_three_le_of_slot0_bound (I := I) (M := M) g T₀ x e K₀ hsplit
      (D₀ ^ 2 * rfnsBudget (I := I) (M := M) g T₀ x) hper
  have hn_E : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by
    rw [hn]; norm_cast
  have hsq : (Real.sqrt (Module.finrank ℝ E) * D₀) ^ 2 =
      (Module.finrank ℝ E : ℝ) * D₀ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hbud_eq : rfnsBudget (I := I) (M := M) g T₀ x =
      (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
          ((covGrad (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := rfl
  rw [hsq, ← hbud_eq]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x
        ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
        ≤ (n : ℝ) * (D₀ ^ 2 * rfnsBudget (I := I) (M := M) g T₀ x) := hle
    _ = (Module.finrank ℝ E : ℝ) * D₀ ^ 2 * rfnsBudget (I := I) (M := M) g T₀ x := by
        rw [hn_E]; ring

end Connection
end Integral
end DifferentialGeometry

end
