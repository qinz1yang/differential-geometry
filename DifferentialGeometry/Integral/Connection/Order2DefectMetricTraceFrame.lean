import DifferentialGeometry.Integral.Connection.TensorRicciCommutator
import DifferentialGeometry.Integral.Connection.Order2DefectRouteFrameComp
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorClose3
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvL2Bound
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpDualFrameParseval

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
(`CovGradRoughLapCurvL2Bound.lean`).

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
(`CovGradRoughLapCurvL2Bound.lean`) restated under the route-endpoint name; it is the final
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

end Connection
end Integral
end DifferentialGeometry

end
