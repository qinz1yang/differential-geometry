import DifferentialGeometry.Integral.Connection.Order2DefectMetricTraceFrame

/-!
# The off-diagonal curvature core of the order-`2` covariant defect

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2`
commutator defect is the `(0, 3)`-tensor field
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)
```
(`CovGradRoughLapCommutatorClose3.lean`), where `Δ_∇ = rawTensorConnLapSmooth` is the rough
(connection) Laplacian and `∇ = covGrad` is the covariant gradient. Its pointwise intrinsic
fibre-norm bound
```
rfns(covGradRoughLapCurv g T₀)(x) ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x)
```
is the only remaining ingredient for the unconditional order-`2` covariant Gårding estimate
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
(`CovGradRoughLapCurvL2Bound.lean`), assembled from this pointwise bound by the endpoint
bridge `hpt_to_unconditional_bound` (`Order2DefectMetricTraceFrame.lean`).

## The genuine off-diagonal curvature

Writing `Δ_∇ T = ∑ᵢ ∇²_{Bᵢ, Bᵢ} T` (the frame trace of the Hessian over a `g_x`-orthonormal
frame `Bᵢ := smoothOrthoFrame g x i`; `rawTensorConnLap_eq_frame_trace_secondCovDeriv`), the
defect rearranges the *gradient* slot of `∇T₀` (its leftmost covariant direction `Z`) past the
two trace slots `(Bᵢ, Bᵢ)`. Each such reorder is a covariant-derivative commutator, governed by
the pointwise tensor Ricci identity (`tensorSecondCovDeriv_antisymm_eq_riemannOp`,
`TensorRicciCommutator.lean`):
```
∇²_{X, Y} S(x) − ∇²_{Y, X} S(x) = R_x(X(x), Y(x)) S(x).
```
The curvature is the **off-diagonal** Riemann operator `R_x(Bᵢ, Z)` with `Z` the gradient
direction (`Z ≠ Bᵢ` generically), *not* the diagonal `R_x(Bᵢ, Bᵢ) = 0`: the diagonal reading
is degenerate (it falsely makes the defect vanish by curvature antisymmetry, the trap that
killed earlier metric-trace attempts), so the genuine content lives in the off-diagonal pair.

This file establishes the off-diagonal curvature core, with full non-degeneracy:

* `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` — **STEP 4, the genuine off-diagonal Ricci
  identity for the gradient tensor `S := ∇T₀`**, at rank `(0, 3)`. For any smooth tangent
  fields `X, Y`, the antisymmetric pair-swap of the second covariant derivative of `S` is the
  bundled Riemann curvature `R_x(X(x), Y(x))(S(x))`. The curvature is honestly off-diagonal:
  for `X = Bᵢ` (a frame direction) and `Y = Z` (the gradient direction) it is the nonzero
  `R_x(Bᵢ, Z)(∇T₀)`, never the vanishing diagonal `R_x(Bᵢ, Bᵢ)`.

* `riemannOp_gradTensor_offDiag_fiberNormSq_le` — **STEP 5, the off-diagonal curvature fibre
  bound**: for **general** directions `v, w` (so `v ≠ w` off-diagonal is covered),
  ```
  rfns(R_x(v, w)(∇T₀(x))) ≤ Cx · g(v, v) · g(w, w) · rfns(∇T₀(x)),
  ```
  via the imported `(0, 3)` Parseval curvature fibre bound
  `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le`.

* `riemannOp_gradTensor_offDiag_frame_fiberNormSq_le` — the off-diagonal bound along the
  orthonormal-frame pair `(Bᵢ, Bⱼ)` (`i ≠ j`), where the `g`-length factors collapse to `1`:
  `rfns(R_x(Bᵢ, Bⱼ)(∇T₀)) ≤ Cx · rfns(∇T₀)`.

* `covGradRoughLapCurv_toSection_eq_sub` — the pointwise frame-free presentation of the defect
  `(covGradRoughLapCurv g T₀).toSection x = Δ_∇(∇T₀)(x) − ∇(Δ_∇ T₀)(x)`, the form on which the
  remaining reconciliation acts.

## The precise remaining subgoal (documented, not assumed)

The off-diagonal curvature core above supplies the genuine curvature term and its fibre bound.
Turning the defect into a sum of off-diagonal curvature contractions plus a `∇R · T₀`-type
lower-order term still requires the metric-compatibility intertwining **STEP 2**:
```
∇ ∘ traceG = traceG ∘ ∇    (cometric parallelism on the `(0, s+2) → (0, s)` metric trace),
```
which lets the outer covariant derivative `∇` pass through the metric trace `Δ_∇ = traceG(∇²·)`
without differentiating the moving frame. STEP 2 is the abstract-tensor metric-parallel property
`∇(g⁻¹) = 0` propagated through the two contracted Hessian slots; it is genuine new content not
present in the available infrastructure and is the single remaining gap. Once STEP 2 is
available, the off-diagonal Ricci identity `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` of
this file together with the per-pair off-diagonal bound
`riemannOp_gradTensor_offDiag_frame_fiberNormSq_le` supply the genuine per-pair off-diagonal
curvature content. Assembling the per-pair contributions into the pointwise `hpt` requires the
gradient direction to occupy a *single* curvature slot — the antisymmetric `(frame, gradient)`
contraction that survives Riemann antisymmetry — rather than a symmetric frame double-trace
(which vanishes identically); that final assembly is left open here.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`, currying the new
tangent-direction slot as the leftmost (gradient) covariant slot. All fibre norms are the
intrinsic Riemannian fibre norm `riemannianFiberNormSq` — never a model-space norm or chart
operator norm, which are genuinely unbounded on multi-chart manifolds.
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

/-- **Frame-free pointwise presentation of the defect.** The underlying section value of the
canonical commutator defect at `x` is the difference of the rough Laplacian of the gradient
tensor and the gradient of the rough Laplacian:
```
(covGradRoughLapCurv g T₀).toSection x
  = (Δ_∇(∇T₀)).toSection x − (∇(Δ_∇ T₀)).toSection x,
```
where `∇T₀ = covGrad g 0 2 T₀`, `Δ_∇(∇T₀) = rawTensorConnLapSmooth g 0 3 (∇T₀)`,
`Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀`, and `∇(Δ_∇ T₀) = covGrad g 0 2 (Δ_∇ T₀)`. -/
theorem covGradRoughLapCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
  rw [covGradRoughLapCurv]
  rw [SmoothCcTensor.toSection_sub]
  rfl

/-- **Frame-trace reading of the rough-Laplacian piece of the defect.** The rough Laplacian of
the `(0, 3)`-tensor gradient field, read at `x`, is the frame trace of its second covariant
derivative over the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`:
```
(Δ_∇(∇T₀)).toSection x = ∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇T₀)(x).
```
This is `rawTensorConnLap_eq_frame_trace_secondCovDeriv` at rank `(0, 3)` applied to the
underlying section of `∇T₀ = covGrad g 0 2 T₀`. -/
theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

/-- **STEP 4 (off-diagonal Ricci identity for the gradient tensor).** Let `S := ∇T₀ =
covGrad g 0 2 T₀` be the rank-`(0, 3)` gradient tensor of `T₀`. For smooth tangent fields
`X, Y`, the antisymmetric pair-swap of the second covariant derivative of `S` is the bundled
Riemann curvature on the fibre values:
$$
  \nabla^2_{X, Y} S(x) - \nabla^2_{Y, X} S(x) = R_x\bigl(X(x), Y(x)\bigr)\,S(x),
$$
with `R_x = riemannOp (tensorCov g 0 3) x`. With `X := Bᵢ` (a frame direction) and `Y := Z`
(the gradient direction) the right-hand side is the genuine **off-diagonal** curvature
`R_x(Bᵢ, Z)(∇T₀)`, which is generically nonzero — never the degenerate diagonal
`R_x(Bᵢ, Bᵢ) = 0`. This is the rank-`(0, 3)` instance of
`tensorSecondCovDeriv_antisymm_eq_riemannOp` on the gradient section. -/
theorem secondCovDeriv_gradTensor_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 3 X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 3 Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 3) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 3
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
    hX hY (covGrad_contMDiff_mk' (I := I) (M := M) g T₀)

/-- **STEP 5 (off-diagonal curvature fibre bound, general directions).** For **any** tangent
vectors `v, w` (in particular the off-diagonal frame pair `v = Bᵢ`, `w = Bⱼ` with `i ≠ j`), the
curvature contraction of the gradient tensor `∇T₀` satisfies
```
rfns(R_x(v, w)(∇T₀(x))) ≤ Cx · g(v, v) · g(w, w) · rfns(∇T₀(x)),
```
with `Cx ≥ 0` the per-point curvature constant of
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le` at rank `(0, 3)`. The constant `Cx` is
uniform in `(v, w)` and in the contracted tensor; the bound is genuinely off-diagonal (no
collinearity of `v, w` is assumed). -/
theorem riemannOp_gradTensor_offDiag_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x v w
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 3 x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)

/-- **STEP 5 along the orthonormal-frame pair.** Specialising the off-diagonal fibre bound to the
frame pair `(Bᵢ, Bⱼ)` (with `Bₖ := smoothOrthoFrame g x k`), the `g`-length factors collapse: for
`i = j` to `1`, and for `i ≠ j` the `g`-inner factor `g(Bᵢ, Bⱼ) = 0` is irrelevant (the bound
multiplies by the *self* inner products `g(Bᵢ, Bᵢ) = g(Bⱼ, Bⱼ) = 1`). Hence
```
rfns(R_x(Bᵢ, Bⱼ)(∇T₀)) ≤ Cx · rfns(∇T₀).
```
This is the off-diagonal curvature bound in the clean frame-collapsed form, with the same uniform
constant `Cx`. -/
theorem riemannOp_gradTensor_offDiag_frame_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannOp_gradTensor_offDiag_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, fun i j => ?_⟩
  have hii : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  have hjj : g.inner x (smoothOrthoFrame (I := I) g x j x)
      (smoothOrthoFrame (I := I) g x j x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x j j
    simpa using this
  have h := hbound (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
  rw [hii, hjj] at h
  simpa using h

end Connection

end Integral

end DifferentialGeometry

end
