import DifferentialGeometry.Integral.Connection.TensorConnLapSecondOrderGardingGen
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorClose3
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Integral.Connection.Tensor3rdCurvFiberNormBound

/-!
# The pointwise-to-`L²` reduction for the curvature defect bound `hcurv`

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, the generalized order-`2` covariant Gårding estimate
`secondCovGrad_l2NormSq_le_rawConnLap_gen` (`TensorConnLapSecondOrderGardingGen.lean`)
consumes a **curvature defect `L²` bound** `hcurv` of the shape
```
‖Curv‖_{L²} ≤ C₀ · (‖T₀‖_{L²} + ‖∇T₀‖_{L²} + ‖∇²T₀‖_{L²}),
```
where `Curv : SmoothCcTensor g 0 3` is the canonical commutator defect
`covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)`, `∇T₀ = covGrad g 0 2 T₀` and
`∇²T₀ = covGrad g 0 3 (covGrad g 0 2 T₀)`.

This file supplies the **analytic packaging** that turns a *pointwise* fibre-norm bound on
the defect — the form in which the genuine third-order Weitzenböck curvature reconciliation
(`Tensor3rdCurv` + the moving-frame residual, `CovGradRoughLapCommutatorClose3.lean`)
delivers its control — into the `L²` inequality of the exact shape consumed by
`secondCovGrad_l2NormSq_le_rawConnLap_gen`. The bridge corollary
`tensorL2Norm_sq_eq_integral_riemannianFiberNormSq`
(`RiemannianFiberNormSqTensorInnerBridge.lean`) converts the squared metric `L²` norm of a
tensor section field into the integral of its intrinsic Riemannian fibre norm; the packaging
then chains: `integral` monotonicity (`MeasureTheory.integral_mono_of_nonneg`), the bridge
corollary on each of the four squared norms, and `Real.sqrt` monotonicity with the elementary
`p² + q² + r² ≤ (p + q + r)²` (`p, q, r ≥ 0`).

## Main results

* `integrable_riemannianFiberNormSq_toSection` — square-integrability of the intrinsic fibre
  norm of a compactly-supported smooth tensor section, transported from `MemL2` of its model
  field through the fibre-norm bridge equality.

* `tensorL2Norm_le_of_pointwise_fiberNormSq_bound` — the headline packaging: from a pointwise
  fibre-norm bound
  `riemannianFiberNormSq g 0 3 x (Curv.toSection x) ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x)`
  (for every `x`, with `C₀ ≥ 0`), conclude the curvature defect `L²` bound `hcurv`
  `‖Curv‖_{L²} ≤ C₀ · (‖T₀‖_{L²} + ‖∇T₀‖_{L²} + ‖∇²T₀‖_{L²})` of the exact shape consumed by
  `secondCovGrad_l2NormSq_le_rawConnLap_gen`.

* `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound` — the Gårding assembly with
  the curvature `L²` bound replaced by its sufficient *pointwise* fibre-norm form: the
  commutator equation `hcomm` is discharged automatically through the canonical defect
  `covGradRoughLapCurv` (`covGradRoughLap_commutator_eq`), and the `L²` bound `hcurv` is
  supplied by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound` from the pointwise hypothesis.

## The remaining gap (documented, not assumed)

The single remaining ingredient for the unconditional `hcurv` — and hence for the
unconditional `secondCovGrad_l2NormSq_le_rawConnLap` (no `hcomm`/`hcurv` hypotheses) — is the
**pointwise** fibre-norm bound
```
riemannianFiberNormSq g 0 3 x (covGradRoughLapCurv g T₀).toSection x
  ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x),
```
the hypothesis of `tensorL2Norm_le_of_pointwise_fiberNormSq_bound` /
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`. That bound is **not** packaged
here: it is the genuine third-order tensor Weitzenböck content. Its closure requires the
slot-`0` Christoffel matching (obstruction 1 of `CovGradRoughLapCommutatorClose2.lean`) — the
torsion-free identification of `Δ_∇(∇T₀)(x)(unit)` (curried) with the fixed-frame trace
`∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)` — followed by the two genuinely-distinct fibre-norm bounds:
the `Tensor3rdCurv` curvature-contraction bound (controlled fibrewise by `rfns(T₀)`,
`rfns(∇T₀)`, `rfns(∇²T₀)` via `Tensor3rdCurvFiberNormBound.lean` and the Parseval curvature
lemmas) and the moving-frame residual bound (`covGradRoughLapMovingFrameResidual`, controlled
by `rfns(∇²T₀)`). Both obstructions are documented as open in
`CovGradRoughLapCommutatorClose{2,3}.lean`; this file isolates the analytic packaging so that
closing them immediately yields the unconditional estimate.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the tensor rank from
`(0, s)` to `(0, s + 1)`. All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq` — never a model-space norm or chart operator norm, which are
genuinely unbounded on multi-chart manifolds.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
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
/-- **Integrability of the intrinsic fibre norm.** For a smooth compactly-supported
`(r, s)`-tensor section `S`, the map `x ↦ riemannianFiberNormSq g r s x (S.toSection x)` is
Bochner-integrable against the Riemannian volume measure. -/
theorem integrable_riemannianFiberNormSq_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hmem := SmoothCcTensor.memL2_toFun (I := I) (M := M) S
  have hmem' :
      MeasureTheory.Integrable
        (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x))
        (riemannianVolumeMeasure (I := I) (M := M) g) := hmem
  refine hmem'.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [SmoothCcTensor.toFun_apply]
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (S.toSection x)).symm

set_option linter.unusedSectionVars false in
/-- **Pointwise-to-`L²` packaging for `hcurv`.** Let `T₀ : SmoothCcTensor g 0 2` and
`Curv : SmoothCcTensor g 0 3`, and let `C₀ ≥ 0`. If, for every `x`, the intrinsic fibre norm
of `Curv` at `x` is bounded by `C₀²` times the sum of the intrinsic fibre norms of `T₀`,
`∇T₀ = covGrad g 0 2 T₀` and `∇²T₀ = covGrad g 0 3 (covGrad g 0 2 T₀)`:
```
riemannianFiberNormSq g 0 3 x (Curv.toSection x)
  ≤ C₀² · ( riemannianFiberNormSq g 0 2 x (T₀.toSection x)
          + riemannianFiberNormSq g 0 3 x ((∇T₀).toSection x)
          + riemannianFiberNormSq g 0 (3 + 1) x ((∇²T₀).toSection x) ),
```
then the curvature defect `L²` bound `hcurv` holds:
```
‖Curv‖_{L²} ≤ C₀ · (‖T₀‖_{L²} + ‖∇T₀‖_{L²} + ‖∇²T₀‖_{L²}).
```
This is the exact `hcurv` hypothesis of `secondCovGrad_l2NormSq_le_rawConnLap_gen`. -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
      C₀ * (tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun +
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun +
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set Hess : SmoothCcTensor g 0 (3 + 1) :=
    covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) with hHess_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun with hnT_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1) Hess.toFun with hnHess_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hbridgeT : nT ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ := by
    rw [hnT_def, hμ_def]
    have hfun : T₀.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 2) (x := x) (T₀.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 2 _
  have hbridgeGrad : nGrad ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ := by
    rw [hnGrad_def, hμ_def]
    have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (S.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hbridgeHess : nHess ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x) ∂μ := by
    rw [hnHess_def, hμ_def]
    have hfun : Hess.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3 + 1) (x := x) (Hess.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) _
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def]
    have hfun : Curv.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (Curv.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hintT := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 2 T₀
  have hintGrad := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 3 S
  have hintHess := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (3 + 1) Hess
  set RHS : M → ℝ := fun x =>
    C₀ ^ 2 *
      (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x))
    with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def, hμ_def]
    exact ((hintT.add hintGrad).add hintHess).const_mul (C₀ ^ 2)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤ RHS x := by
    intro x
    rw [hRHS_def, hS_def, hHess_def]
    exact hpt x
  have hcurv_nn : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn hRHS_int
      (Filter.Eventually.of_forall hpt')
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        C₀ ^ 2 *
          ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ)) := by
    rw [hRHS_def]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hsplit12 :
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) =
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) :=
      MeasureTheory.integral_add hintT hintGrad
    have hsplit123 :
        (∫ x, ((riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x)) ∂μ) =
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ) :=
      MeasureTheory.integral_add (hintT.add hintGrad) hintHess
    rw [hsplit123, hsplit12]
  have hsq_bound : nCurv ^ 2 ≤ C₀ ^ 2 * (nT ^ 2 + nGrad ^ 2 + nHess ^ 2) := by
    rw [hbridgeCurv, hbridgeT, hbridgeGrad, hbridgeHess]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C₀ ^ 2 *
            ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
                (Hess.toSection x) ∂μ)) := hRHS_integral
  clear_value nT nGrad nHess nCurv
  have hy_nn : 0 ≤ C₀ * (nT + nGrad + nHess) :=
    mul_nonneg hC₀ (by linarith [hnT_nn, hnGrad_nn, hnHess_nn])
  have hfinal_sq : nCurv ^ 2 ≤ (C₀ * (nT + nGrad + nHess)) ^ 2 := by
    refine le_trans hsq_bound ?_
    have hcross : nT ^ 2 + nGrad ^ 2 + nHess ^ 2 ≤ (nT + nGrad + nHess) ^ 2 := by
      nlinarith [mul_nonneg hnT_nn hnGrad_nn, mul_nonneg hnT_nn hnHess_nn,
        mul_nonneg hnGrad_nn hnHess_nn]
    nlinarith [mul_le_mul_of_nonneg_left hcross (sq_nonneg C₀), sq_nonneg C₀]
  nlinarith [hfinal_sq, hnCurv_nn, hy_nn, sq_nonneg (nCurv - C₀ * (nT + nGrad + nHess))]

set_option linter.unusedSectionVars false in
/-- **Order-`2` covariant Gårding estimate from a pointwise curvature defect bound.** Let `g`
be a smooth Riemannian metric on a closed manifold `M` and `T₀ : SmoothCcTensor g 0 2`. If the
canonical commutator defect `covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)` satisfies the
pointwise fibre-norm bound
```
riemannianFiberNormSq g 0 3 x (covGradRoughLapCurv g T₀).toSection x
  ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x)
```
for every `x`, with `C₀ ≥ 0`, then
```
‖∇²T₀‖²_{L²} ≤ (2 + 3 C₀ + 2 C₀²) · (‖Δ_∇ T₀‖²_{L²} + ‖T₀‖²_{L²}),
```
where `∇²T₀ = covGrad g 0 3 (covGrad g 0 2 T₀)`, `∇T₀ = covGrad g 0 2 T₀`, and
`Δ_∇ T₀ = rawTensorConnLapSmooth g 0 2 T₀`. The commutator equation `hcomm` is discharged
through `covGradRoughLap_commutator_eq`; the curvature `L²` bound `hcurv` is discharged from
the pointwise hypothesis through `tensorL2Norm_le_of_pointwise_fiberNormSq_bound`. -/
theorem secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound
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
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) := by
  refine secondCovGrad_l2NormSq_le_rawConnLap_gen (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀
    (covGradRoughLap_commutator_eq (I := I) (M := M) g T₀) ?_
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀ hpt

end Connection
end Integral
end DifferentialGeometry

end
