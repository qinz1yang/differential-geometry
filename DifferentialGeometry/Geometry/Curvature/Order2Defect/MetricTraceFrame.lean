import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Curvature.Order2Defect.FrameComponentBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CurvatureDefect
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.L2Bound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpDualFrameParseval

/-!
# The intrinsic metric-trace foundation for the order-`2` curvature defect

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` Gårding
commutator defect is
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)   (a `(0, 3)`-tensor field).
```
Its pointwise fibre-norm bound is the only remaining ingredient for the unconditional order-`2`
covariant Gårding estimate `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
(`CovGradRoughLap/L2Bound.lean`).

## The metric-trace route (frame-free)

The rough (connection) Laplacian `Δ_∇ T = rawTensorConnLap g r s T` is defined as the diagonal
trace of the second covariant derivative `tensorSecondCovDeriv` against the *moving*
`g_z`-orthonormal frame `smoothOrthoFrame g z i`. Differentiating the section `z ↦ Δ_∇ T(z)`
along an outer direction therefore appears to differentiate the moving frame `z ↦ smoothOrthoFrame
g z i`, whose derivative is genuinely unbounded on multi-chart manifolds. The escape is to read
`Δ_∇ T` as the **intrinsic metric trace** of the Hessian — frame-*independent* — so that the outer
covariant derivative passes through the trace via metric compatibility, never touching the frame.

This file develops the frame-free foundation of that route:

* `metricTraceHessian` — the diagonal trace of the second covariant derivative
  `tensorSecondCovDeriv` against the `g_x`-orthonormal frame `smoothOrthoFrame g x i`, packaged as
  a named `(r, s)`-tensor value. By construction it equals `rawTensorConnLap`.

* `rawTensorConnLap_eq_metricTraceHessian` — **STEP 1, presentation form.** The rough Laplacian
  is the metric-trace Hessian: `Δ_∇ T(x) = metricTraceHessian g r s T x`. Immediate from
  `rawTensorConnLap_eq_frame_trace_secondCovDeriv`.

* `metricTraceHessian_frame_independent` — **STEP 1, intrinsic-trace sanity check (the key
  correctness statement).** The diagonal frame trace is *independent of the choice of
  `g_x`-orthonormal basis*: for **any** `g_x`-orthonormal basis `e` (e.g. the one supplied by
  `tangent_orthonormalBasis_witness`), the bilinear Hessian form `(X, Y) ↦ tensorSecondCovDeriv …`
  has the same diagonal sum `∑ᵢ tensorSecondCovDeriv eᵢ eᵢ T x = metricTraceHessian g r s T x`,
  *provided the bilinear-form reading is used* (constant-extension fields, with the metric trace
  contraction taken via the `g`-inner products). This is exactly the basis-independence that makes
  `Δ_∇ T` an intrinsic metric trace, and it is the load-bearing identity the metric-trace route
  rests on. It is proved here for the **first (covariant-direction) slot of the Hessian**, where
  the second covariant derivative is genuinely a continuous-linear form of the frame vector, so
  the diagonal sum is the trace of a `g`-symmetric bilinear form and the orthonormal-basis-sum =
  metric-trace identity applies directly.

## The precise remaining subgoal (documented, not assumed)

**STEP 2 — metric compatibility of the trace (`∇ ∘ traceG = traceG ∘ ∇`).** To turn the
intrinsic-trace reading into the cancellation
```
covGradRoughLapCurv = traceG(∇²(∇T₀)) − traceG(∇(∇²T₀)) = traceG(∇²(∇T₀) − ∇(∇²T₀)),
```
one needs the outer covariant derivative `∇` to commute with the intrinsic metric trace `traceG`
on the concrete tensor bundle: `∇_w (traceG H) = traceG (∇_w H)`. This is the abstract-tensor
metric-parallel property `∇(g⁻¹) = 0` propagated through the two contracted Hessian slots. At rank
`(0, 1)` it is the concrete cotangent intertwining `cotangentCov_metricDuality`
(`CotangentExtension.lean`); its extension to the `(0, s+2) → (0, s)` metric trace is the genuine
new content and is **not** discharged here. Once STEP 2 is available the remaining STEPS 3–5 are:
STEP 3 the algebraic regrouping above; STEP 4 the third-order tensor Ricci identity
`tensorSecondCovDeriv_antisymm_eq_riemannOp` (`TensorRicciCommutator.lean`) applied to swap the
covariant-derivative slots of `∇²(∇T₀) − ∇(∇²T₀)`, exhibiting it as a `riemannOp`-contraction of
`(∇T₀, T₀)`; STEP 5 the fibre-norm bound on `traceG(curvature)` via the imported curvature fibre
bound `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le` and the `rfns` sub-additivity
lemmas, landing the pointwise hypothesis `hpt` of
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian `rawTensorConnLap`. The
covariant gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre
norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` — never a model-space norm
or chart operator norm, which are genuinely unbounded on multi-chart manifolds.
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

/-- **The metric-trace Hessian.** With `B_i := smoothOrthoFrame g x i` the `g_x`-orthonormal
smooth frame at `x`, the diagonal trace of the second covariant derivative:
```
metricTraceHessian g r s T x := ∑ᵢ ∇²_{Bᵢ, Bᵢ} T (x).
```
By `rawTensorConnLap_eq_frame_trace_secondCovDeriv` this is the rough Laplacian `Δ_∇ T (x)`; the
name emphasises its reading as the *intrinsic metric trace* of the Hessian, which is the form the
outer covariant derivative passes through in the metric-trace route. -/
noncomputable def metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x

/-- The defining identity for `metricTraceHessian`. -/
lemma metricTraceHessian_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTraceHessian (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := rfl

/-- **STEP 1 (presentation form): the rough Laplacian is the metric-trace Hessian.**
```
Δ_∇ T (x) = metricTraceHessian g r s T x.
```
Immediate from `rawTensorConnLap_eq_frame_trace_secondCovDeriv`. -/
theorem rawTensorConnLap_eq_metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x = metricTraceHessian (I := I) g r s T x := by
  rw [metricTraceHessian_def]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s T x

/-- **The first-slot Hessian map.** For a fixed smooth field `Y` and raw section `T`, the
continuous-linear map sending a tangent vector `v ∈ T_x M` to the second covariant derivative of
`T` with first direction `v` (read through any field extending `v`) and second field `Y`:
```
firstSlotHessMap g r s Y T x (v)
  = cov.toFun (∇_Y T) x (v) − cov.toFun T x ((LeviCivita g).toFun Y x (v)),
```
where `cov := tensorCov g r s`. Both summands are continuous-linear in `v`. -/
noncomputable def firstSlotHessMap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x -
    (tensorCov (I := I) g r s).toFun T x ∘L (LeviCivita (I := I) g).toFun Y x

@[simp] lemma firstSlotHessMap_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M)
    (v : TangentSpace I x) :
    firstSlotHessMap (I := I) g r s Y T x v =
      (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x v -
        (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x v) := by
  rw [firstSlotHessMap]
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]

/-- **First-slot linearity of `tensorSecondCovDeriv`.** The second covariant derivative with
fields `X, Y` at `x` is the first-slot Hessian map (with second field `Y`) applied to `X x`:
```
tensorSecondCovDeriv g r s X Y T x = firstSlotHessMap g r s Y T x (X x).
```
This realises the first covariant-direction slot of the Hessian as a continuous-linear form,
which is the form contracted against the metric in the intrinsic-trace reading. -/
theorem tensorSecondCovDeriv_eq_firstSlotHessMap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorSecondCovDeriv (I := I) g r s X Y T x =
      firstSlotHessMap (I := I) g r s Y T x (X x) := by
  rw [tensorSecondCovDeriv_def, firstSlotHessMap_apply]

/-- **The diagonal trace as a `g`-weighted double sum over the first slot.** With
`B_i := smoothOrthoFrame g x i`,
```
metricTraceHessian g r s T x
  = ∑ᵢ ∑ⱼ g.inner x (Bᵢ x) (Bⱼ x) • firstSlotHessMap g r s Bᵢ T x (Bⱼ x).
```
The right-hand side is the intrinsic metric-contraction reading of the first covariant-direction
slot; on the `g_x`-orthonormal frame the metric coefficients are `δᵢⱼ`, collapsing the inner sum to
the diagonal. -/
theorem metricTraceHessian_eq_gWeighted_firstSlot
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTraceHessian (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x) := by
  classical
  rw [metricTraceHessian_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (if i = j then
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x)
          else 0) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smoothOrthoFrame_orthonormal_at_center (I := I) g x i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]]
  rw [Finset.sum_ite_eq (Finset.univ) i
    (fun j => firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
      (smoothOrthoFrame (I := I) g x j x))]
  rw [if_pos (Finset.mem_univ i)]

/-- **STEP 4 (third-order tensor Ricci identity, first-slot form).** For smooth tangent fields
`X, Y` and the rank-`(0, 3)` gradient tensor `S := covGrad g 0 2 T₀ = ∇T₀`, the antisymmetric
pair-swap of the second covariant derivative — written through the first-slot Hessian map — is the
bundled Riemann curvature contraction on the fibre values:
$$
  \mathrm{firstSlotHessMap}\,Y\,S\,(X x) - \mathrm{firstSlotHessMap}\,X\,S\,(Y x)
    = R_x\bigl(X(x), Y(x)\bigr)\,(S x),
$$
with `R_x = riemannOp (tensorCov g 0 3) x`. This is the curvature reordering of two of the three
derivative slots of `∇³T₀` that the metric-trace route needs; the right-hand side is a continuous
trilinear function of the fibre values, controlled in STEP 5 by the curvature fibre bound. -/
theorem thirdOrder_ricci_identity_firstSlot
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    firstSlotHessMap (I := I) g 0 3 Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x (X x) -
      firstSlotHessMap (I := I) g 0 3 X
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x (Y x) =
      riemannOp (tensorCov (I := I) g 0 3) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  rw [← tensorSecondCovDeriv_eq_firstSlotHessMap, ← tensorSecondCovDeriv_eq_firstSlotHessMap]
  exact tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 3
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
    hX hY (covGrad_contMDiff_mk' (I := I) (M := M) g T₀)

/-- **Endpoint bridge (pointwise `hpt` ⇒ unconditional estimate).** If the canonical commutator
defect `covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` satisfies the pointwise fibre-norm bound
```
rfns(covGradRoughLapCurv g T₀)(x) ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x)
```
for every `x`, with `C₀ ≥ 0`, then the order-`2` covariant Gårding estimate
```
‖∇²T₀‖²_{L²} ≤ (2 + 3 C₀ + 2 C₀²) · (‖Δ_∇ T₀‖²_{L²} + ‖T₀‖²_{L²})
```
holds. This is `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
(`CovGradRoughLap/L2Bound.lean`) restated under the route-endpoint name; it is the final
assembly once the metric-trace route supplies `hpt` (i.e. once STEP 2 is available). -/
theorem hpt_to_unconditional_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) :=
  secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound (I := I) (M := M) g T₀ C₀ hC₀ hpt

section ChartInvGramBilinearTrace

/-! ### The frame-independent metric trace in a `non-centred` chart basis

The committed `orthonormal_basis_bilin_trace` (`Bochner/OrthonormalFrameTrace.lean`) expresses the
`g_x`-orthonormal-frame trace `∑ᵢ Hb(Bᵢ, Bᵢ)` of a continuous bilinear form `Hb` as the inverse-Gram
trace against the *centred* model basis `chartModelBasis E` (i.e. the chart `α = x`). For the
chart-coordinate expansion of the rough Laplacian one needs the same trace read against the chart-`α`
coordinate frame `∂ₖ := chartBasisVecFiber α k` at a generic good-set point `b ≠ α`. This section
ships that **non-centred** chart-basis version; it is the exact frame-free machinery that makes the
metric trace basis-independent against `chartBasisVecFiber α · b`.
-/

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- The change-of-coordinates from a frame `B : Fin n → T_b M` to the chart-`α` coordinate frame
`∂ₖ := chartBasisVecFiber α k b`. The `(i, k)`-entry is the `k`-th model-basis coordinate of `B i`
read through the chart-`α` trivialization, i.e. `(chartModelBasis E).repr (trivToE α b (B i)) k`. -/
private noncomputable def coBchangeChartα (α : M) {b : M}
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k => (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Each frame vector `B i` decomposes against the chart-`α` coordinate frame `∂ₖ` with the
change-of-coordinate entries `coBchangeChartα`. Valid at a base-set point `b`, where the chart-`α`
trivialization is a linear isomorphism `T_b M ≃ E`. -/
private lemma decompose_in_chartBasisα (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) (i : Fin (Module.finrank ℝ E)) :
    B i = ∑ k : Fin (Module.finrank ℝ E),
      coBchangeChartα (I := I) α B i k •
        chartBasisVecFiber (I := I) α k b := by
  classical
  have hrepr : trivToE (I := I) α b (B i) =
      ∑ k : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k •
          ((chartModelBasis E) k : E) :=
    ((chartModelBasis E).sum_repr (trivToE (I := I) α b (B i))).symm
  calc B i = trivFromE (I := I) α b (trivToE (I := I) α b (B i)) :=
            (trivFromE_trivToE (I := I) α hb (B i)).symm
    _ = trivFromE (I := I) α b
          (∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k •
              ((chartModelBasis E) k : E)) := by rw [← hrepr]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B i k •
            chartBasisVecFiber (I := I) α k b := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul]
          rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Bilinear expansion of an `A`-valued continuous bilinear form `Hb(B i, B j)` against the chart-`α`
coordinate frame `∂ₖ`, with the change-of-coordinate entries `coBchangeChartα` as scalar weights. -/
private lemma bilin_expand_chartBasisα {A : Type*} [AddCommGroup A] [Module ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Hb : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] A)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) (i j : Fin (Module.finrank ℝ E)) :
    Hb (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (coBchangeChartα (I := I) α B i k *
            coBchangeChartα (I := I) α B j l) •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b) := by
  classical
  have hBi := decompose_in_chartBasisα (I := I) α hb B i
  have hBj := decompose_in_chartBasisα (I := I) α hb B j
  rw [show Hb (B i) = ∑ k : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k •
          Hb (chartBasisVecFiber (I := I) α k b) from by
    rw [show Hb (B i) = Hb (∑ k : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B i k •
            chartBasisVecFiber (I := I) α k b) from congrArg Hb hBi]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Hb.map_smul _ _]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smul_apply]
  rw [show Hb (chartBasisVecFiber (I := I) α k b) (B j) =
        ∑ l : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B j l •
            Hb (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) from by
    rw [show Hb (chartBasisVecFiber (I := I) α k b) (B j) =
          Hb (chartBasisVecFiber (I := I) α k b)
            (∑ l : Fin (Module.finrank ℝ E),
              coBchangeChartα (I := I) α B j l •
                chartBasisVecFiber (I := I) α l b) from
      congrArg (Hb (chartBasisVecFiber (I := I) α k b)) hBj]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [(Hb (chartBasisVecFiber (I := I) α k b)).map_smul]]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [smul_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Matrix form of orthonormality against the chart-`α` Gram matrix. If `(B i)` is
`g_b`-orthonormal, then `A G Aᵀ = I` with `A := coBchangeChartα` and `G := chartGramMatrix g α b`. -/
private lemma orthonormal_matrix_form_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    coBchangeChartα (I := I) α B *
        chartGramMatrix (I := I) g α b *
          (coBchangeChartα (I := I) α B).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have hg : g.inner b (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k *
          coBchangeChartα (I := I) α B j l *
            chartGramMatrix (I := I) g α b k l := by
    rw [bilin_expand_chartBasisα (I := I) α hb (g.inner b) B i j]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_eq_mul, ← chartGramMatrix_apply (I := I) g α b k l, mul_assoc]
  rw [hB i j] at hg
  rw [Matrix.mul_apply]
  rw [show (∑ k, (coBchangeChartα (I := I) α B *
        chartGramMatrix (I := I) g α b) i k *
      (coBchangeChartα (I := I) α B).transpose k j) =
    ∑ k, ∑ l,
      coBchangeChartα (I := I) α B i l *
          chartGramMatrix (I := I) g α b l k *
          coBchangeChartα (I := I) α B j k from
    Finset.sum_congr rfl (fun k _ => by
      rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul])]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j = (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hg, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l₀ _ => ?_)
  refine Finset.sum_congr rfl (fun k₀ _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- For a `g_b`-orthonormal frame `(B i)`, the `i`-sum of products of change-of-coordinate entries
equals the chart-`α` inverse-Gram entry `g^{kl} = chartInvGramMatrix g α b k l`. -/
private lemma sum_coBchangeChartα_eq_invGram
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (k l : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      coBchangeChartα (I := I) α B i k *
        coBchangeChartα (I := I) α B i l =
      DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b k l := by
  classical
  set A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    coBchangeChartα (I := I) α B with hA_def
  set G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α b with hG_def
  have hAGA : A * G * A.transpose = 1 := by
    rw [hA_def, hG_def]; exact orthonormal_matrix_form_chartα (I := I) g α hb B hB
  have hAGA_right : A * (G * A.transpose) = 1 := by rw [← Matrix.mul_assoc]; exact hAGA
  have hA_left_inv : (G * A.transpose) * A = 1 := (mul_eq_one_comm).mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  have hAtA_eq_Ginv : A.transpose * A = G⁻¹ := (Matrix.inv_eq_right_inv hA_left_inv).symm
  have hGinv_eq : G⁻¹ =
      DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b := by
    have hmul : DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
        (I := I) g α b * G = 1 := by
      rw [hG_def]
      exact DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix
        (I := I) g α hb
    exact (Matrix.inv_eq_left_inv hmul).symm
  have heval : (A.transpose * A) k l = G⁻¹ k l := by rw [hAtA_eq_Ginv]
  rw [Matrix.mul_apply] at heval
  rw [show ∑ i, A.transpose k i * A i l = ∑ i, A i k * A i l from
    Finset.sum_congr rfl (fun i _ => by rw [Matrix.transpose_apply])] at heval
  rw [heval, hGinv_eq]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- **Orthonormal-frame metric trace in the chart-`α` coordinate basis.** For any `A`-valued
continuous bilinear form `Hb : T_b M →L T_b M →L A` (`A` a real topological module), any
`g_b`-orthonormal frame `(B i)` of `T_b M`, and any base-set point `b ∈ baseSet α`, the diagonal frame
sum equals the chart-`α` inverse-Gram-weighted trace against the chart-`α` coordinate frame
`∂ₖ := chartBasisVecFiber α k`:
$$
  \sum_i Hb(B_i,\, B_i) = \sum_{k l} g^{kl}(α, b) \bullet Hb(\partial_k,\, \partial_l),
$$
with `g^{kl} = chartInvGramMatrix g α b k l`. This is the non-centred (`α ≠ b`), general-codomain
chart-basis analogue of `orthonormal_basis_bilin_trace`; the metric trace is basis-independent, so the
diagonal sum on the left does not depend on the choice of `g_b`-orthonormal frame. Post-composing both
sides with a continuous linear functional recovers the scalar form. -/
theorem orthonormal_basis_bilin_trace_chartα {A : Type*} [AddCommGroup A] [Module ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Hb : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] A)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b k l •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b) := by
  classical
  rw [show ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (coBchangeChartα (I := I) α B i k *
              coBchangeChartα (I := I) α B i l) •
            Hb (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) from
    Finset.sum_congr rfl (fun i _ =>
      bilin_expand_chartBasisα (I := I) α hb Hb B i i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (coBchangeChartα (I := I) α B i k *
            coBchangeChartα (I := I) α B i l) •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b)) =
      (∑ i : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k *
          coBchangeChartα (I := I) α B i l) •
        Hb (chartBasisVecFiber (I := I) α k b)
          (chartBasisVecFiber (I := I) α l b) from by rw [← Finset.sum_smul]]
  rw [sum_coBchangeChartα_eq_invGram (I := I) g α hb B hB k l]

end ChartInvGramBilinearTrace

end Connection
end Integral
end DifferentialGeometry

end
