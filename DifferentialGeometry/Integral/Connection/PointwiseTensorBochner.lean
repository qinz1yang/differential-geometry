import DifferentialGeometry.Integral.Connection.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Integral.Connection.Order2DefectGradientSlotLeibniz
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound
import DifferentialGeometry.Integral.Connection.TensorThirdOrderWeitzenbock

/-!
# The rank-generic pointwise tensor Bochner–Weitzenböck representation

This file builds the **rank-generic** pointwise tensor Bochner–Weitzenböck
representation of the order-`2` commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S),
```

the `(0, s + 1)`-tensor field appearing in the integrated order-`2` Weitzenböck
identity, at *arbitrary* covariant rank `s` (the existing development isolates the
specialised rank `s = 2` object `covGradRoughLapCurv`). Writing
`∇S := covGrad g 0 s S`, `Δ_∇ T := rawTensorConnLapSmooth g 0 s T`, and
`B_i := smoothOrthoFrame g x i` for the smooth `g_x`-orthonormal frame, the section
value of the defect is the fixed-frame sum of per-summand third-order differences:

```
Curv S (x) = ∑ᵢ [ ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇(∇²_{Bᵢ, Bᵢ} S)(x) ].
```

Here `∇²_{Bᵢ, Bᵢ}(∇S)` is the rank-`(0, s + 1)` second covariant derivative of the
gradient tensor `∇S` (its leftmost / gradient slot differentiated by the
`(0, s + 1)`-bundle connection) and `∇(∇²_{Bᵢ, Bᵢ} S)` is the `(0, s + 1)`-tensor
covariant gradient of the rank-`(0, s)` second covariant derivative of `S`. Each
per-summand difference is the gradient-slot reordering of the three covariant
derivative slots, the genuine off-diagonal Riemann curvature — the true
third-order tensor Bochner–Weitzenböck term, in which both the pure-`R` contraction
`R(Bᵢ, ·)(∇_{Bᵢ} S)` *and* the genuine curvature-derivative contraction
`(∇_{Bᵢ} R)(Bᵢ, ·) S` are present.

## Main results

* `pointwiseTensorCurv` — the rank-generic order-`2` commutator defect
  `Δ_∇(∇S) − ∇(Δ_∇ S)` as a `(0, s + 1)`-tensor field (`SmoothCcTensor g 0 (s + 1)`).
* `pointwiseTensorCurv_commutator_eq` — the commutator equation
  `Δ_∇(∇S) = ∇(Δ_∇ S) + Curv S`.
* `pointwiseTensorCurv_toSection_eq_sub` — the section value of the defect as the
  pointwise difference of the two `(0, s + 1)` fields.
* `pointwiseTensorCurv_toSection_eq_frame_sum` — **representation (A)**: the
  section value of the defect as the fixed-frame sum of per-summand third-order
  differences (no moving-frame derivative survives).

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace, `rawTensorConnLapSmooth`).
The covariant gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to
`(0, s + 1)`, currying the new tangent-direction slot as the leftmost covariant
slot. All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

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

/-- **The rank-generic order-`2` commutator defect.** The difference of the rough
Laplacian of the `(0, s + 1)`-tensor gradient field `∇S` and the covariant gradient
of the rough Laplacian of `S`, as a smooth compactly-supported `(0, s + 1)`-tensor
field:
```
pointwiseTensorCurv g s S := Δ_∇(∇S) − ∇(Δ_∇ S).
```
At rank `s = 2` it is `covGradRoughLapCurv g S`; this is its rank-generic lift, the
canonical witness for the commutator equation consumed by the generalized order-`2`
Gårding / Weitzenböck estimate. -/
noncomputable def pointwiseTensorCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)

/-- **The commutator equation** (`hcomm`). For the rank-generic defect
`pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)`,
```
Δ_∇(∇S) = ∇(Δ_∇ S) + pointwiseTensorCurv g s S,
```
by `sub_add_cancel`. -/
theorem pointwiseTensorCurv_commutator_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)
        + pointwiseTensorCurv (I := I) (M := M) g s S := by
  set A : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) with hA
  set B : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hB
  change A = B + (A - B)
  abel

/-- **The section value of the defect as a pointwise difference.** The underlying
section value of `pointwiseTensorCurv g s S` at `x` is the difference of the two
`(0, s + 1)` section values
```
(pointwiseTensorCurv g s S).toSection x
  = (Δ_∇(∇S)).toSection x − (∇(Δ_∇ S)).toSection x.
```
-/
theorem pointwiseTensorCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x := by
  have hdef : (pointwiseTensorCurv (I := I) (M := M) g s S) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := rfl
  rw [hdef, SmoothCcTensor.toSection_sub]
  rfl

/-- **Frame-trace reading of the rough-Laplacian piece.** The rough Laplacian of the
`(0, s + 1)`-tensor gradient field `∇S`, read at `x`, is the frame trace of its
second covariant derivative over the `g_x`-orthonormal frame `Bᵢ`:
```
(Δ_∇(∇S)).toSection x = ∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇S)(x).
```
This is `rawTensorConnLap_eq_frame_trace_secondCovDeriv` at rank `(0, s + 1)` applied
to the underlying section of `∇S = covGrad g 0 s S`. -/
theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 (s + 1)
    (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x

/-- **The gradient piece as a fixed-frame sum of per-summand covariant gradients.**
The covariant gradient `∇(Δ_∇ S)` of the rough Laplacian (the section of
`covGrad g 0 s (Δ_∇ S)`) equals, at `x`, the fixed-frame sum of the covariant
gradients of the per-summand second covariant derivatives:
```
(covGrad g 0 s (Δ_∇ S)).toSection x
  = ∑ᵢ covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)).
```
This is `covGradBundleEquiv_covDeriv_rawConnLap_eq_sum` at `r = 0`, rank `s`, read
through `covGrad_toSection_apply` and `rawTensorConnLapSmooth_toSection_apply`. -/
theorem covGrad_rawConnLap_toSection_eq_frame_sum_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) 0 s x
          ((tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x) := by
  have hS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 s S).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g 0 s (fun z : M => S.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g 0 s hS x

/-- **Representation (A): the rank-generic defect as a fixed-frame sum of per-summand
third-order differences.** The underlying section value of the order-`2` commutator
defect at `x` is the fixed-frame sum
```
(pointwiseTensorCurv g s S).toSection x
  = ∑ᵢ [ ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)) ],
```
with `Bᵢ := smoothOrthoFrame g x i`. The first per-summand term is the rank-`(0, s + 1)`
second covariant derivative of the gradient tensor `∇S` (whose leftmost / gradient slot
is differentiated by the `(0, s + 1)`-bundle connection); the second is the
`(0, s + 1)`-tensor covariant gradient of the per-summand `(0, s)` second covariant
derivative `∇²_{Bᵢ, Bᵢ} S`. Their difference is the *gradient-slot* reordering of the
three covariant derivative slots — the genuine off-diagonal Riemann curvature. The proof
splits the defect by `pointwiseTensorCurv_toSection_eq_sub`, reads the rough-Laplacian
piece by `rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen`, the gradient piece by
`covGrad_rawConnLap_toSection_eq_frame_sum_gen`, and combines the two frame sums via
`Finset.sum_sub_distrib`. No moving-frame derivative survives. -/
theorem pointwiseTensorCurv_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x)) := by
  classical
  rw [pointwiseTensorCurv_toSection_eq_sub (I := I) (M := M) g s S x]
  rw [rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen (I := I) (M := M) g s S x]
  rw [covGrad_rawConnLap_toSection_eq_frame_sum_gen (I := I) (M := M) g s S x]
  rw [← Finset.sum_sub_distrib]

/-- **The pointwise fibre pairing of the defect against the gradient field.** At `x`, the
metric-induced fibre pairing of the order-`2` commutator defect `Curv S (x)` against the
gradient field `∇S(x) = (covGrad g 0 s S)(x)`, written as the pointwise inner product
`tensorInnerPointwise` of the trivialized model tensors. This is the pointwise integrand of
the curvature cross term `⟨Curv, ∇S⟩_{L²}`. -/
noncomputable def pointwiseTensorCurvPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))

/-- The pointwise fibre pairing `pointwiseTensorCurvPairing` is exactly the pointwise model
pairing of the function-coercions `(Curv S).toFun` and `(∇S).toFun`, the integrand of the
`L²` cross term `tensorL2Inner g 0 (s + 1) (Curv S).toFun (∇S).toFun`. -/
lemma pointwiseTensorCurvPairing_eq_toFun
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    pointwiseTensorCurvPairing (I := I) (M := M) g s S x =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  rfl

/-- **Fibre Cauchy–Schwarz for the defect pairing.** The absolute value of the pointwise fibre
pairing of `Curv S (x)` against `∇S(x)` is bounded by the geometric mean of the two intrinsic
Riemannian fibre norms:
```
| g_x(Curv S (x), ∇S(x)) | ≤ √(rfns(Curv S)(x)) · √(rfns(∇S)(x)).
```
This is the pointwise Cauchy–Schwarz inequality `abs_tensorInnerPointwise_le_mul` read through
the fibre-norm bridge `riemannianFiberNormSq_eq_tensorInnerPointwise` (which identifies the
diagonal pairing of a trivialized model tensor with the intrinsic fibre norm). -/
theorem abs_pointwiseTensorCurvPairing_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  rw [pointwiseTensorCurvPairing]
  have hcs := abs_tensorInnerPointwise_le_mul (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))
  rw [tensorPointwiseNorm, tensorPointwiseNorm,
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x),
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x)] at hcs
  exact hcs

/-- **The headline pointwise pairing bound (B).** Let `K_R, K_dR ≥ 0` and suppose the
intrinsic fibre norm of the order-`2` commutator defect `Curv S` at `x` satisfies the genuine
third-order tensor Bochner–Weitzenböck per-point bound (the pure-`R` term controlled by
`K_R · √(rfns(∇S))` and the curvature-derivative `∇R` term controlled by `K_dR · √(rfns(S))`):
```
√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x)).
```
Then the pointwise fibre pairing of the defect against the gradient field is bounded in the
exact shape consumed by the curvature cross-term reduction:
```
| g_x(Curv S (x), ∇S(x)) |
  ≤ K_R · rfns(∇S)(x) + K_dR · √(rfns(S)(x)) · √(rfns(∇S)(x)).
```
The proof is fibre Cauchy–Schwarz `abs_pointwiseTensorCurvPairing_le`
(`| g_x(Curv, ∇S) | ≤ √(rfns(Curv)) · √(rfns(∇S))`), the per-point fibre-norm hypothesis on
the first factor, and the distributive law on the resulting product
`(K_R √(rfns(∇S)) + K_dR √(rfns(S))) · √(rfns(∇S))`, using `√(rfns(∇S)) · √(rfns(∇S)) =
rfns(∇S)` by non-negativity of the fibre norm. The `∇²S`-order discrepancy of the defect is
**not** present in this bound: it is absorbed entirely into the per-point fibre-norm hypothesis
on `√(rfns(Curv S))`, which is the genuine curvature representation supplied by the caller
(at the `L²` level the discrepancy integrates by parts; this pointwise statement consumes its
curvature-controlled fibre-norm bound directly). -/
theorem pointwiseTensorCurv_pairing_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (K_R K_dR : ℝ)
    (hfibre :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x))) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) *
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  set sqCurv : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) with hsqCurv
  set sqGrad : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x)) with hsqGrad
  set sqS : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))
    with hsqS
  have hsqGrad_nn : 0 ≤ sqGrad := Real.sqrt_nonneg _
  have hgrad_sq : sqGrad * sqGrad =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    rw [hsqGrad]
    exact Real.mul_self_sqrt
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  have hcs := abs_pointwiseTensorCurvPairing_le (I := I) (M := M) g s S x
  rw [← hsqCurv, ← hsqGrad] at hcs
  calc |pointwiseTensorCurvPairing (I := I) (M := M) g s S x|
      ≤ sqCurv * sqGrad := hcs
    _ ≤ (K_R * sqGrad + K_dR * sqS) * sqGrad :=
        mul_le_mul_of_nonneg_right hfibre hsqGrad_nn
    _ = K_R * (sqGrad * sqGrad) + K_dR * sqS * sqGrad := by ring
    _ = K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
          K_dR * sqS * sqGrad := by rw [hgrad_sq]

/-- **The genuine third-order curvature field (R and ∇R).** The two genuine curvature
contributions inside `Tensor3rdCurv W T x`, summed over the `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i`:
```
tensor3rdCurvGenuine g r s W T x
  := ∑ᵢ ( R(Bᵢ, W)(∇_{Bᵢ} T)(x) + ∇_{Bᵢ}(R(Bᵢ, W) T)(x) ).
```
The first summand `riemannSec (tensorCov g r s) Bᵢ W (∇_{Bᵢ} T)` is the pure Riemann curvature
acting on the once-derived tensor (a `rfns(∇T)`-order term); the second summand
`∇_{Bᵢ}(R(Bᵢ, W) T)` is the covariant derivative of the curvature section — the genuine `∇R`
term — whose Leibniz expansion `(∇_{Bᵢ} R)(Bᵢ, W) T + R(Bᵢ, W)(∇_{Bᵢ} T)` carries the
`rfns(T)`-order curvature-derivative contribution. This is the true third-order tensor
Bochner–Weitzenböck curvature, with `∇R` genuinely present. -/
noncomputable def tensor3rdCurvGenuine
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x))

/-- **The frame-bracket discrepancy of the third-order curvature field.** The two frame-bracket
contributions inside `Tensor3rdCurv W T x`, summed over the `g_x`-orthonormal frame:
```
tensor3rdCurvBracket g r s W T x
  := ∑ᵢ ( ∇_{[Bᵢ, W]}(∇_{Bᵢ} T)(x) + ∇_{Bᵢ}(∇_{[Bᵢ, W]} T)(x) ).
```
Both summands carry the frame-bracket `[Bᵢ, W]` and are `∇²T`-order in `T`; this is the
discrepancy that the pointwise representation cannot remove (the slot-`0` frame-trace matching is
mathematically false on a normal manifold). At the `L²` level it integrates by parts; the
pointwise statements name it explicitly. -/
noncomputable def tensor3rdCurvBracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
        (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
      + (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
          (smoothOrthoFrame (I := I) g x i x))

/-- **`Tensor3rdCurv` splits into its genuine-curvature and bracket-discrepancy parts.** The
explicit third-order curvature field is the sum of its two genuine curvature contributions
(`tensor3rdCurvGenuine`, the `R` and `∇R` terms) and its two frame-bracket terms
(`tensor3rdCurvBracket`, the `∇²T`-order discrepancy):
```
Tensor3rdCurv W T x = tensor3rdCurvGenuine W T x + tensor3rdCurvBracket W T x.
```
This is a reordering of the four summands of `Tensor3rdCurv_def` inside the frame sum
(`Finset.sum_add_distrib` and commutativity of fibre addition). -/
theorem Tensor3rdCurv_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    Tensor3rdCurv (I := I) g r s W T x =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  classical
  rw [Tensor3rdCurv_def, tensor3rdCurvGenuine, tensor3rdCurvBracket,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  abel

/-- **The directional-`W` third-order Weitzenböck representation, genuine-curvature form, at
arbitrary rank.** The directional-`W` reading of the order-`2` commutator defect — the difference
of the frame-trace third covariant derivative `∑ᵢ ∇_{Bᵢ} ∇_{Bᵢ}(∇_W T)` and its swapped form
`∑ᵢ ∇_W ∇_{Bᵢ} ∇_{Bᵢ} T` — equals the genuine curvature field (the `R` and `∇R` contractions)
plus the named frame-bracket discrepancy:
```
∑ᵢ ∇_{Bᵢ} ∇_{Bᵢ}(∇_W T)(x) − ∑ᵢ ∇_W ∇_{Bᵢ} ∇_{Bᵢ} T (x)
  = tensor3rdCurvGenuine W T x + tensor3rdCurvBracket W T x.
```
This is `frame_trace_thirdCovDeriv_swap` (the rank-generic third-order Weitzenböck commutator)
with `Tensor3rdCurv` resolved into its genuine-curvature and bracket-discrepancy parts by
`Tensor3rdCurv_eq_genuine_add_bracket`. Both `R` and `∇R` are genuinely present in the
`tensor3rdCurvGenuine` term; the `∇²T`-order discrepancy is the explicitly named
`tensor3rdCurvBracket` term. -/
theorem frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g r s) W T)) x
            (smoothOrthoFrame (I := I) g x i x)) -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g r s).toFun
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T)) x
              (W x)) =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  rw [frame_trace_thirdCovDeriv_swap (I := I) g r s hW hT,
    Tensor3rdCurv_eq_genuine_add_bracket (I := I) g r s W T x]
  abel

/-- **Fibre-norm bound for the genuine third-order curvature field.** Fix `x` and write
`Bᵢ := smoothOrthoFrame g x i`, `n := Module.finrank ℝ E`. Suppose the two genuine per-summand
curvature contributions are controlled, for every `i`, by the per-point pure-curvature constant
`cR` (the `R`-contraction, `rfns(∇T)`-order, automatically nonnegative as a fibre-norm upper
bound) and the per-point curvature-derivative constant `cdR` (the `∇R`-term, `rfns(T)`-order):
```
rfns( R(Bᵢ, W)(∇_{Bᵢ} T)(x) ) ≤ cR,
rfns( ∇_{Bᵢ}(R(Bᵢ, W) T)(x) ) ≤ cdR.
```
Then the genuine third-order curvature field is fibre-norm-bounded by
```
rfns( tensor3rdCurvGenuine W T x ) ≤ (2 n) · n · (cR + cdR).
```
The proof bounds the frame sum by the `n`-sub-additivity `riemannianFiberNormSq_sum_le_card_mul`,
then each per-summand sum-of-two by `riemannianFiberNormSq_add_le`, then sums the per-`i`
constants. The constants `cR`, `cdR` are the per-point curvature / curvature-derivative bounds
the caller supplies from the uniform sups `‖R‖_∞ · rfns(∇T)`, `‖∇R‖_∞ · rfns(T)`. -/
theorem riemannianFiberNormSq_tensor3rdCurvGenuine_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M)
    (cR cdR : ℝ)
    (hR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) ≤ cR)
    (hdR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          ((tensorCov (I := I) g r s).toFun
            (fun b : M => riemannSec (tensorCov (I := I) g r s)
              (smoothOrthoFrame (I := I) g x i) W T b) x
            (smoothOrthoFrame (I := I) g x i x)) ≤ cdR) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (tensor3rdCurvGenuine (I := I) g r s W T x) ≤
      (2 * (Module.finrank ℝ E : ℝ)) * (Module.finrank ℝ E : ℝ) * (cR + cdR) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set F : Fin n → TensorRSSpace r s I x := fun i =>
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x) with hF
  have hsum : tensor3rdCurvGenuine (I := I) g r s W T x = ∑ i : Fin n, F i := rfl
  rw [hsum]
  have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r s x
    (Finset.univ : Finset (Fin n)) F
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤ 2 * (cR + cdR) := by
    intro i
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x
      (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x)
      ((tensorCov (I := I) g r s).toFun
        (fun b : M => riemannSec (tensorCov (I := I) g r s)
          (smoothOrthoFrame (I := I) g x i) W T b) x
        (smoothOrthoFrame (I := I) g x i x))
    have h1 := hR i
    have h2 := hdR i
    calc riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              ((tensorCov (I := I) g r s).toFun
                (fun b : M => riemannSec (tensorCov (I := I) g r s)
                  (smoothOrthoFrame (I := I) g x i) W T b) x
                (smoothOrthoFrame (I := I) g x i x)) := hadd
      _ ≤ 2 * cR + 2 * cdR := by
            have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
            have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
            linarith
      _ = 2 * (cR + cdR) := by ring
  have hsum_le : ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤
      (n : ℝ) * (2 * (cR + cdR)) := by
    calc ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ ∑ _i : Fin n, (2 * (cR + cdR)) := Finset.sum_le_sum (fun i _ => hper i)
      _ = (n : ℝ) * (2 * (cR + cdR)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (∑ i : Fin n, F i)
      ≤ (n : ℝ) * ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) := hcard
    _ ≤ (n : ℝ) * ((n : ℝ) * (2 * (cR + cdR))) :=
        mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = (2 * (n : ℝ)) * (n : ℝ) * (cR + cdR) := by ring

/-- **The pure-`R` curvature term in bundled-operator form, on the frame.** The per-summand
pure Riemann curvature contribution `R(Bᵢ, W)(∇_{Bᵢ} T)(x)` of the genuine third-order curvature
field is the bundled curvature operator `riemannOp (tensorCov g r s) x` evaluated on the fibre
values `(Bᵢ x, W x, (∇_{Bᵢ} T)(x))`:
```
riemannSec (tensorCov g r s) Bᵢ W (∇_{Bᵢ} T) x
  = riemannOp (tensorCov g r s) x (Bᵢ x) (W x) ((∇_{Bᵢ} T)(x)).
```
This is the Gårding-ready form: a continuous trilinear function of the fibre values whose fibre
norm is controlled by the uniform `‖R‖_∞ · rfns(∇T)` via
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le`. It is
`riemannSec_eq_riemannOp_tensorCov` at `X := Bᵢ`, with the once-derived section `∇_{Bᵢ} T` and
its smoothness supplied by `covApplyRS_contMDiff`. -/
theorem tensor3rdCurv_pure_R_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x =
      riemannOp (tensorCov (I := I) g r s) x
        (smoothOrthoFrame (I := I) g x i x) (W x)
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T x) := by
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T b)) :=
    covApplyRS_contMDiff (I := I) g r s hT hB
  exact riemannSec_eq_riemannOp_tensorCov (I := I) g r s hB hW hZ

end Connection
end Integral
end DifferentialGeometry

end
