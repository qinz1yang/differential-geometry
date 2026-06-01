import DifferentialGeometry.Integral.Connection.Order2DefectStep2PT_Direct

/-!
# The partial metric-trace covariant-derivative commutation (final, `g`-weighted route)

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
this file develops the **partial metric-trace covariant-derivative commutation** — the last
ingredient needed to convert the canonical order-`2` covariant Gårding defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` into a sum of off-diagonal Riemann-curvature
contractions of `∇T₀`.

## The geometric input that makes the route work

The single fact that powers the route is that the smooth `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i` is `g_y`-orthonormal *for every `y` in its orthonormality
neighbourhood `smoothOrthoFrameNbhd x`*, not merely at the centre `x`
(`smoothOrthoFrame_orthonormal`). Consequently the metric-trace Hessian, read as the diagonal
frame sum against `Bᵢ`, is a *neighbourhood* formula:
```
Δ_∇ T (y) = ∑ᵢ firstSlotHessMap g r s Bᵢ T y (Bᵢ y)      (y ∈ smoothOrthoFrameNbhd x),
```
with the *same* `x`-centred frame `Bᵢ` valid throughout the neighbourhood. This is the form the
outer covariant derivative `∇_w` can be applied to, since the frame is fixed (the metric weights
`g(Bᵢ y, Bⱼ y) = δᵢⱼ` are *locally constant*, `frame_pairing_locally_const`, so differentiating
them produces the cometric skew core which vanishes by `cometric_skew_core`).

## What this file establishes

* `firstSlotHessMap_eq_secondCovDeriv_field` — the per-summand bridge
  `firstSlotHessMap g r s Y T y (X y) = tensorSecondCovDeriv g r s X Y T y` between the first-slot
  Hessian map reading and the `tensorSecondCovDeriv` reading, at an arbitrary point `y`.

* `frozenFrameTrace` — the diagonal sum of the second covariant derivative over the *fixed,
  `x`-centred* smooth orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, read at a point `y`:
  `∑ᵢ tensorSecondCovDeriv g r s Bᵢ Bᵢ T y`. Because the frame is fixed, this is a smooth section
  in `y`, so the outer covariant derivative `∇_w` acts on it with *no* moving-frame derivative.

* `frozenFrameTrace_self_eq_metricTrace2` — at the centre `y = x`, the frame-frozen diagonal sum is
  the partial metric trace `metricTrace2 g r s (tensorSecondCovDeriv) T x`, hence (via
  `rawTensorConnLap_eq_metricTrace2`) the rough Laplacian `Δ_∇ T x`.

* `frozenFrameTrace_eq_gWeighted_of_mem_nbhd` — the **neighbourhood-valid `g`-weighted reading**:
  for every `y ∈ smoothOrthoFrameNbhd x`, the frame-frozen diagonal sum equals the `g`-weighted
  double sum `∑ᵢⱼ g(Bᵢ y, Bⱼ y) • firstSlotHessMap g r s Bᵢ T y (Bⱼ y)`. This is the genuine new
  foundation that the earlier `slot0FrameTraceMatching` route lacked: it is valid throughout the
  neighbourhood (not only at the centre `x`), with the metric weights locally constant, so the
  outer `∇` differentiates it with the moving-frame correction governed by `cometric_skew_core`.

## The precise remaining subgoal (documented, not assumed)

The fully-discharged `∇`-commutation
```
tensorCovDerivAt g r s (frozenFrameTrace g r s T x ·) x w
  = ∑ᵢ tensorCovDerivAt g r s (y ↦ tensorSecondCovDeriv g r s Bᵢ Bᵢ T y) x w
```
— the statement that the outer covariant derivative passes through the *fixed-frame* diagonal sum
(immediate from covariant additivity over the finite frame sum, since the frame is fixed) — and the
**frame-independence bridge** `frozenFrameTrace g r s T x y = rawTensorConnLap g r s T y` for
`y ∈ smoothOrthoFrameNbhd x` (the metric trace `∑ᵢ ∇²_{eᵢ, eᵢ} T y` is independent of the choice of
`g_y`-orthonormal frame, comparing the `x`-centred frame `Bᵢ` with the `y`-centred frame
`smoothOrthoFrame g y i`), together convert the canonical defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` into the third-order frame-trace commutator. Each
slot swap is then the off-diagonal Ricci identity `secondCovDeriv_gradTensor_antisymm_eq_riemannOp`,
and the frame-summed fibre norm is bounded by `frame_offDiag_curvature_sum_fiberNormSq_le`, landing
the pointwise `hpt`; `hpt_to_unconditional_bound` then yields the unconditional estimate. The
frame-independence bridge (a tensor-valued metric-trace basis-invariance, the
`metricTraceHessian_frame_independent` content) and the covariant-additivity differentiation are the
genuine remaining content; this file supplies the neighbourhood `g`-weighted reading and the
per-summand identification on which they rest.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre norms are the
intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

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

/-- **Per-summand identification.** The diagonal `firstSlotHessMap` summand against a vector `v`
is the second covariant derivative with both direction slots `v`:
```
firstSlotHessMap g r s Y T y (v) = tensorSecondCovDeriv g r s (· ↦ v as field) Y T y,
```
read at the point `y` through the first-slot Hessian map. Specialising to `Y := Bᵢ` and
`v := Bᵢ y` (with `Bᵢ := smoothOrthoFrame g x i`) gives the diagonal trace summand. -/
theorem firstSlotHessMap_eq_secondCovDeriv_field
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (y : M) :
    firstSlotHessMap (I := I) g r s Y T y (X y) =
      tensorSecondCovDeriv (I := I) g r s X Y T y := by
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]

/-- **The frame-frozen diagonal sum.** The diagonal sum of the second covariant derivative over the
fixed `x`-centred smooth orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, read at a point `y`:
```
frozenFrameTrace g r s T x y := ∑ᵢ tensorSecondCovDeriv g r s Bᵢ Bᵢ T y.
```
At the centre `y = x` it is the metric trace `metricTrace2 g r s (tensorSecondCovDeriv) T x =
Δ_∇ T x`; for `y` in the orthonormality neighbourhood it equals the `g`-weighted reading, and it is
a smooth section of the tensor bundle (the frame is a fixed smooth field), so the outer covariant
derivative `∇_w` can be applied to it directly. -/
noncomputable def frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    TensorRSSpace r s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y

/-- The defining identity for `frozenFrameTrace`. -/
lemma frozenFrameTrace_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y := rfl

/-- **At the centre, the frame-frozen diagonal sum is the metric trace.** Read at `y = x`, the
frame-frozen diagonal sum coincides with the partial metric trace of the second covariant
derivative, hence (`rawTensorConnLap_eq_metricTrace2`) with the rough Laplacian `Δ_∇ T x`. -/
theorem frozenFrameTrace_self_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    frozenFrameTrace (I := I) g r s T x x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [frozenFrameTrace_def, metricTrace2_def]

/-- **The frame-frozen diagonal sum equals its `g`-weighted reading on the neighbourhood.** For
every `y` in the orthonormality neighbourhood `smoothOrthoFrameNbhd x`, the diagonal sum over the
fixed `x`-centred frame equals the `g`-weighted double sum
```
∑ᵢ ∑ⱼ g(Bᵢ y, Bⱼ y) • firstSlotHessMap g r s Bᵢ T y (Bⱼ y),
```
since the frame is `g_y`-orthonormal at `y` (`smoothOrthoFrame_orthonormal`), so the metric weights
are `δᵢⱼ` and the inner `j`-sum collapses to the diagonal. This is the neighbourhood-valid
`g`-weighted reading — the form the outer covariant derivative differentiates, with the
moving-frame correction governed by `cometric_skew_core`. -/
theorem frozenFrameTrace_eq_gWeighted_of_mem_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y) := by
  classical
  rw [frozenFrameTrace_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (if i = j then
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)
          else 0) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smoothOrthoFrame_orthonormal (I := I) g x hy i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]]
  rw [Finset.sum_ite_eq (Finset.univ) i
    (fun j => firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
      (smoothOrthoFrame (I := I) g x j y))]
  rw [if_pos (Finset.mem_univ i)]

end Connection
end Integral
end DifferentialGeometry

end
