import DifferentialGeometry.Integral.Connection.TensorConnLapGreenDivergenceIdentity
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.Pairing.CauchySchwarz

/-!
# The order-`1` covariant-gradient `L²` control from the `(0, 2)` Green identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file extracts, from the integrated `(0, 2)`
connection-Laplacian Green identity
`green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed`, the first-order
elliptic-regularity inequality

```
‖∇T‖²_{L²} ≤ ‖Δ_∇ T‖_{L²} · ‖T‖_{L²}
```

for every smooth compactly-supported `(0, 2)`-tensor field `T`. This is the
genuine order-`1` interior control by the order-`2` (rough-Laplacian / `L²`)
data: it is the load-bearing first half of the order-`2` Gårding estimate. The
full Gårding estimate additionally needs the second-covariant-derivative
(`∇²T`) `L²` control, which requires a `(0, 3)`-level integration by parts and
is not derived here.

## The mechanism

Specialising the Green identity at `v := T` gives
`⟨∇T, ∇T⟩_{L²} = − ⟨Δ_∇ T, T⟩_{L²}`. The left side is the squared `L²` norm of
the covariant gradient (a non-negative quantity); the right side is bounded in
absolute value, via the global Cauchy–Schwarz inequality `abs_tensorL2Inner_le`
together with the square-integrability of smooth compactly-supported sections
(`memL2_toFun`, `integrable_inner_cross`), by `‖Δ_∇ T‖_{L²} · ‖T‖_{L²}`.

## Main results

* `tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner` — the diagonal Green
  identity `⟨∇T, ∇T⟩_{L²} = − ⟨Δ_∇ T, T⟩_{L²}`.
* `covGrad_l2NormSq_le_rawConnLap_mul_self` — the headline first-order control
  `‖∇T‖²_{L²} ≤ ‖Δ_∇ T‖_{L²} · ‖T‖_{L²}`.
* `covGrad_l2Norm_le_geomMean` — its square-rooted form.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 2` raises the
tensor rank from `(0, 2)` to `(0, 3)`; its diagonal `L²` self-pairing is the
squared `L²` norm of the iterated covariant derivative `∇T`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

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
/-- The squared metric `L²` norm of the underlying field of a smooth
compactly-supported `(r, s)`-tensor section equals its `L²` self-pairing. The
self-pairing is non-negative, so its square root recovers the norm. -/
lemma tensorL2Norm_sq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  rw [tensorL2Norm_def]
  exact Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun)

set_option linter.unusedSectionVars false in
/-- **Diagonal `(0, 2)` Green identity.** For a smooth compactly-supported
`(0, 2)`-tensor field `T`, the diagonal `L²` self-pairing of the covariant
gradient equals minus the `L²` pairing of the rough Laplacian with `T`:

```
⟨∇T, ∇T⟩_{L²} = − ⟨Δ_∇ T, T⟩_{L²}.
```
-/
lemma tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 T).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun T.toFun :=
  green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T T

set_option linter.unusedSectionVars false in
/-- **First-order covariant-gradient `L²` control.** For a smooth
compactly-supported `(0, 2)`-tensor field `T`, the squared `L²` norm of the
covariant gradient is bounded by the product of the `L²` norms of the rough
Laplacian and of `T`:

```
‖∇T‖²_{L²} ≤ ‖Δ_∇ T‖_{L²} · ‖T‖_{L²}.
```

This is the order-`1` interior elliptic estimate by the order-`2`
(rough-Laplacian) data — the first half of the order-`2` Gårding estimate.
The proof is the diagonal `(0, 2)` Green identity combined with the global
`L²` Cauchy–Schwarz inequality. -/
theorem covGrad_l2NormSq_le_rawConnLap_mul_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
        tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
  set ΔT : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T with hΔT_def
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T)]
    rw [hΔT_def]
    exact tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner (I := I) (M := M) g T
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 2 ΔT.toFun T.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔT)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔT T)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs

set_option linter.unusedSectionVars false in
/-- **First-order covariant-gradient `L²` control, square-rooted form.** For a
smooth compactly-supported `(0, 2)`-tensor field `T`,

```
‖∇T‖_{L²} ≤ √(‖Δ_∇ T‖_{L²} · ‖T‖_{L²}).
```
-/
theorem covGrad_l2Norm_le_geomMean
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ≤
      Real.sqrt
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun) := by
  have hsq := covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have hnn : 0 ≤ tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T).toFun :=
    tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1) _
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

end Connection
end Integral
end DifferentialGeometry

end
