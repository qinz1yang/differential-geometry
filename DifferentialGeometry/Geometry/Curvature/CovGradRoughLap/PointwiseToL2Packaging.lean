import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert

/-!
# Pointwise-to-`L²` packaging for tensor fibre-norm bounds (valence-generic)

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
purely analytic **pointwise-to-`L²` packaging** that turns a *pointwise* intrinsic Riemannian
fibre-norm bound on a smooth compactly-supported tensor section into the corresponding `L²`
(semi)norm bound, at arbitrary covariant valence and for an arbitrary finite family of jet terms.

The engine is the fibre-norm bridge `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq`
(`‖S‖² = ∫ rfns(S)`, identifying the squared metric `L²` norm with the integral of the intrinsic
Riemannian fibre norm), combined with integral monotonicity, additivity, and the elementary
arithmetic inequality `∑ⱼ pⱼ² ≤ (∑ⱼ pⱼ)²` for nonnegative `pⱼ`. No curvature content is involved
here; this is the analytic packaging that the genuine curvature fibre-norm bounds feed.

## Main results

* `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three` — the three-term packaging: from a
  pointwise bound `rfns(Curv)(x) ≤ C² · (rfns(A) + rfns(B) + rfns(D))(x)` (every `x`, `C ≥ 0`),
  conclude `‖Curv‖ ≤ C · (‖A‖ + ‖B‖ + ‖D‖)`. The three jet terms `A, B, D` may carry distinct
  valences.

* `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` — the finite-sum packaging: from a pointwise
  bound `rfns(Curv)(x) ≤ C² · (∑_{i < N} rfns(Tᵢ)(x))` (every `x`, `C ≥ 0`), conclude
  `‖Curv‖ ≤ C · ∑_{i < N} ‖Tᵢ‖`, where `Tᵢ : SmoothCcTensor g 0 (vᵢ)` is a family of jet terms with
  per-index valences `vᵢ`.

## Sign / convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq`; the metric `L²`
(semi)norm of a `SmoothCcTensor` is `tensorL2Norm g 0 s S.toFun = ‖S‖`.
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
/-- The squared metric `L²` norm of a `SmoothCcTensor` is the integral of its intrinsic fibre
norm. This is the fibre-norm bridge `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq` read on
the underlying section of a `SmoothCcTensor` (`S.toFun = fun x => toModel (S.toSection x)`). -/
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := 0) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 s _

set_option linter.unusedSectionVars false in
/-- **Integrability of the intrinsic fibre norm.** For a smooth compactly-supported
`(r, s)`-tensor section `S`, the map `x ↦ riemannianFiberNormSq g r s x (S.toSection x)` is
Bochner-integrable against the Riemannian volume measure. Transported from `MemL2` of its model
field through the fibre-norm bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`. -/
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
/-- **Three-term pointwise-to-`L²` packaging.** Let `A : SmoothCcTensor g 0 a`,
`B : SmoothCcTensor g 0 b`, `D : SmoothCcTensor g 0 d`, `Curv : SmoothCcTensor g 0 c`, and let
`C ≥ 0`. If, for every `x`, the intrinsic fibre norm of `Curv` at `x` is bounded by `C²` times the
sum of the intrinsic fibre norms of `A`, `B`, `D`:
```
rfns(Curv)(x) ≤ C² · ( rfns(A)(x) + rfns(B)(x) + rfns(D)(x) ),
```
then the metric `L²` (semi)norms satisfy
```
‖Curv‖ ≤ C · ( ‖A‖ + ‖B‖ + ‖D‖ ).
```
This is the analytic packaging that lifts a genuine pointwise curvature fibre-norm bound to the
`L²` operator bound. -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three
    (g : SmoothRiemannianMetric I M) {a b c d : ℕ}
    (A : SmoothCcTensor g 0 a) (B : SmoothCcTensor g 0 b) (D : SmoothCcTensor g 0 d)
    (Curv : SmoothCcTensor g 0 c) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤
        C ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x))) :
    ‖Curv‖ ≤ C * (‖A‖ + ‖B‖ + ‖D‖) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  rw [SmoothCcTensor.norm_def (I := I) (M := M) A,
    SmoothCcTensor.norm_def (I := I) (M := M) B,
    SmoothCcTensor.norm_def (I := I) (M := M) D,
    SmoothCcTensor.norm_def (I := I) (M := M) Curv]
  set nA : ℝ := tensorL2Norm (I := I) (M := M) g 0 a A.toFun with hnA_def
  set nB : ℝ := tensorL2Norm (I := I) (M := M) g 0 b B.toFun with hnB_def
  set nD : ℝ := tensorL2Norm (I := I) (M := M) g 0 d D.toFun with hnD_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 c Curv.toFun with hnCurv_def
  have hnA_nn : 0 ≤ nA := tensorL2Norm_nonneg (I := I) (M := M) g 0 a _
  have hnB_nn : 0 ≤ nB := tensorL2Norm_nonneg (I := I) (M := M) g 0 b _
  have hnD_nn : 0 ≤ nD := tensorL2Norm_nonneg (I := I) (M := M) g 0 d _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 c _
  have hbridgeA : nA ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ := by
    rw [hnA_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g a A
  have hbridgeB : nB ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ := by
    rw [hnB_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g b B
  have hbridgeD : nD ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x) ∂μ := by
    rw [hnD_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g d D
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g c Curv
  have hintA := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 a A
  have hintB := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 b B
  have hintD := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 d D
  set RHS : M → ℝ := fun x =>
    C ^ 2 *
      (riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x))
    with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def, hμ_def]
    exact ((hintA.add hintB).add hintD).const_mul (C ^ 2)
  have hcurv_nn : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 c x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn hRHS_int
      (Filter.Eventually.of_forall hpt)
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        C ^ 2 *
          ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x) ∂μ)) := by
    rw [hRHS_def, MeasureTheory.integral_const_mul]
    congr 1
    have hsplitAB :
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) ∂μ) =
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) :=
      MeasureTheory.integral_add hintA hintB
    have hsplitABD :
        (∫ x, ((riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) +
            riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x)) ∂μ) =
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x) ∂μ) :=
      MeasureTheory.integral_add (hintA.add hintB) hintD
    rw [hsplitABD, hsplitAB]
  have hsq_bound : nCurv ^ 2 ≤ C ^ 2 * (nA ^ 2 + nB ^ 2 + nD ^ 2) := by
    rw [hbridgeCurv, hbridgeA, hbridgeB, hbridgeD]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C ^ 2 *
            ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 d x (D.toSection x) ∂μ)) :=
          hRHS_integral
  clear_value nA nB nD nCurv
  have hy_nn : 0 ≤ C * (nA + nB + nD) :=
    mul_nonneg hC (by linarith [hnA_nn, hnB_nn, hnD_nn])
  have hfinal_sq : nCurv ^ 2 ≤ (C * (nA + nB + nD)) ^ 2 := by
    refine le_trans hsq_bound ?_
    have hcross : nA ^ 2 + nB ^ 2 + nD ^ 2 ≤ (nA + nB + nD) ^ 2 := by
      nlinarith [mul_nonneg hnA_nn hnB_nn, mul_nonneg hnA_nn hnD_nn,
        mul_nonneg hnB_nn hnD_nn]
    nlinarith [mul_le_mul_of_nonneg_left hcross (sq_nonneg C), sq_nonneg C]
  nlinarith [hfinal_sq, hnCurv_nn, hy_nn, sq_nonneg (nCurv - C * (nA + nB + nD))]

set_option linter.unusedSectionVars false in
/-- **Two-term pointwise-to-`L²` packaging.** Let `A : SmoothCcTensor g 0 a`,
`B : SmoothCcTensor g 0 b`, `Curv : SmoothCcTensor g 0 c`, and let `C ≥ 0`. If
`rfns(Curv)(x) ≤ C² · ( rfns(A)(x) + rfns(B)(x) )` for every `x`, then `‖Curv‖ ≤ C · (‖A‖ + ‖B‖)`.
This is the two-term specialization of `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three`
(taking the third term to be the zero tensor, whose fibre norm vanishes). -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two
    (g : SmoothRiemannianMetric I M) {a b c : ℕ}
    (A : SmoothCcTensor g 0 a) (B : SmoothCcTensor g 0 b)
    (Curv : SmoothCcTensor g 0 c) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤
        C ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x))) :
    ‖Curv‖ ≤ C * (‖A‖ + ‖B‖) := by
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three (I := I) (M := M) g
    A B (0 : SmoothCcTensor g 0 b) Curv C hC (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 b x
        ((0 : SmoothCcTensor g 0 b).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 b x
    rw [hz, add_zero]; exact hpt x

set_option linter.unusedSectionVars false in
/-- **Finite-sum pointwise-to-`L²` packaging.** Let `N : ℕ`, let `v : ℕ → ℕ` be a per-index
valence assignment, let `T : ∀ i, SmoothCcTensor g 0 (v i)` be a finite family of jet terms, let
`Curv : SmoothCcTensor g 0 c`, and let `C ≥ 0`. If, for every `x`, the intrinsic fibre norm of
`Curv` at `x` is bounded by `C²` times the sum of the intrinsic fibre norms of the `Tᵢ`,
```
rfns(Curv)(x) ≤ C² · ∑_{i < N} rfns(Tᵢ)(x),
```
then the metric `L²` (semi)norms satisfy
```
‖Curv‖ ≤ C · ∑_{i < N} ‖Tᵢ‖.
```
This is the `N`-term analytic packaging that lifts a genuine pointwise curvature-derivative
fibre-norm bound to the `L²` operator bound used by the all-order commutator-defect recursion. -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum
    (g : SmoothRiemannianMetric I M) {c : ℕ} (N : ℕ) (v : ℕ → ℕ)
    (T : ∀ i, SmoothCcTensor g 0 (v i)) (Curv : SmoothCcTensor g 0 c) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤
        C ^ 2 * ∑ i ∈ Finset.range N,
          riemannianFiberNormSq (I := I) (M := M) g 0 (v i) x ((T i).toSection x)) :
    ‖Curv‖ ≤ C * ∑ i ∈ Finset.range N, ‖T i‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  rw [SmoothCcTensor.norm_def (I := I) (M := M) Curv]
  conv_rhs => rw [show (fun i => ‖T i‖) = fun i => tensorL2Norm (I := I) (M := M) g 0 (v i) (T i).toFun from by
    funext i; exact SmoothCcTensor.norm_def (I := I) (M := M) (T i)]
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 c Curv.toFun with hnCurv_def
  set fi : ℕ → ℝ := fun i => tensorL2Norm (I := I) (M := M) g 0 (v i) (T i).toFun with hfi_def
  have hfi_nn : ∀ i, 0 ≤ fi i := fun i => tensorL2Norm_nonneg (I := I) (M := M) g 0 (v i) _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 c _
  set gi : ℕ → M → ℝ := fun i x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (v i) x ((T i).toSection x) with hgi_def
  have hint_i : ∀ i, MeasureTheory.Integrable (gi i) μ := by
    intro i; rw [hgi_def, hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (v i) (T i)
  have hbridge_i : ∀ i, fi i ^ 2 = ∫ x, gi i x ∂μ := by
    intro i; rw [hfi_def, hgi_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (v i) (T i)
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g c Curv
  set RHS : M → ℝ := fun x => C ^ 2 * ∑ i ∈ Finset.range N, gi i x with hRHS_def
  have hsum_int : MeasureTheory.Integrable (fun x => ∑ i ∈ Finset.range N, gi i x) μ :=
    MeasureTheory.integrable_finset_sum (Finset.range N) (fun i _ => hint_i i)
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def]; exact hsum_int.const_mul (C ^ 2)
  have hcurv_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 c x _)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤ RHS x := by
    intro x; rw [hRHS_def, hgi_def]; exact hpt x
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn_ae hRHS_int
      (Filter.Eventually.of_forall hpt')
  have hRHS_integral :
      (∫ x, RHS x ∂μ) = C ^ 2 * ∑ i ∈ Finset.range N, ∫ x, gi i x ∂μ := by
    rw [hRHS_def, MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finset_sum (Finset.range N) (fun i _ => hint_i i)
  have hsq_bound : nCurv ^ 2 ≤ C ^ 2 * ∑ i ∈ Finset.range N, fi i ^ 2 := by
    rw [hbridgeCurv]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C ^ 2 * ∑ i ∈ Finset.range N, ∫ x, gi i x ∂μ := hRHS_integral
      _ = C ^ 2 * ∑ i ∈ Finset.range N, fi i ^ 2 := by
            congr 1
            exact Finset.sum_congr rfl (fun i _ => (hbridge_i i).symm)

  have hsum_sq_le : ∑ i ∈ Finset.range N, fi i ^ 2 ≤ (∑ i ∈ Finset.range N, fi i) ^ 2 := by
    have hsq_sum : (∑ i ∈ Finset.range N, fi i) ^ 2 =
        ∑ i ∈ Finset.range N, fi i * (∑ j ∈ Finset.range N, fi j) := by
      rw [pow_two, Finset.sum_mul]
    rw [hsq_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hle : fi i ≤ ∑ j ∈ Finset.range N, fi j :=
      Finset.single_le_sum (f := fun j => fi j) (fun j _ => hfi_nn j) hi
    calc fi i ^ 2 = fi i * fi i := by rw [pow_two]
      _ ≤ fi i * (∑ j ∈ Finset.range N, fi j) :=
          mul_le_mul_of_nonneg_left hle (hfi_nn i)
  clear_value nCurv fi
  set S : ℝ := ∑ i ∈ Finset.range N, fi i with hS_def
  have hS_nn : 0 ≤ S := hS_def ▸ Finset.sum_nonneg (fun i _ => hfi_nn i)
  have hy_nn : 0 ≤ C * S := mul_nonneg hC hS_nn
  have hfinal_sq : nCurv ^ 2 ≤ (C * S) ^ 2 := by
    refine le_trans hsq_bound ?_
    calc C ^ 2 * ∑ i ∈ Finset.range N, fi i ^ 2
        ≤ C ^ 2 * S ^ 2 := by
          rw [hS_def]; exact mul_le_mul_of_nonneg_left hsum_sq_le (sq_nonneg C)
      _ = (C * S) ^ 2 := by ring
  nlinarith [hfinal_sq, hnCurv_nn, hy_nn, sq_nonneg (nCurv - C * S)]

end Connection
end Integral
end DifferentialGeometry

end
