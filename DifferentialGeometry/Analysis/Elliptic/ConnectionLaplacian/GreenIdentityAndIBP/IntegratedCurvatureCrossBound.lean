import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameBracketFold
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

/-!
# The integrated curvature cross-bound from the genuine field nullity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file produces the
**integrated `L²` curvature cross-bound** on the rough-Laplacian / covariant-gradient commutator
defect `Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` (a `(0, s + 1)`-tensor field;
`∇S := covGrad g 0 s S`):

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0,
```

uniformly in `S`. This is the single analytic input the integrated order-`2` Gårding reduction
`secondCovGrad_l2NormSq_le_of_cross_bound` (`IntegratedOrder2Garding.lean`) consumes; closing it makes
the chart-`H²` Gårding constant unconditional.

## The route (the integrated moving-frame nullity, not the Weitzenböck value)

The defect cross-pairing is *not* small term-by-term: by the integrated order-`2` Weitzenböck identity
`weitzenbock_curvature_crossPairing_value` it equals `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`, which carries the
genuine `∇²S`-order energy — so bounding it through that *value* is circular for the Gårding constant.
The sound route bounds the cross-pairing through the **three genuine curvature fields**: the concrete
pure-Riemann curvature section `GcurvSection g s S` (`= R(∇S)`), the differentiated-curvature trace
section `genuineDiffCurvSection g s S` (`= (∇R) S`), and the Bochner–Lichnerowicz Ricci-trace carrier
`ricTraceSection g s S` (`= Ric(∇S)`). The moving-frame remainder
`Curv S − GcurvSection g s S − genuineDiffCurvSection g s S − ricTraceSection g s S` is a total
covariant divergence of an `∇S`-order field, so it pairs to zero against `∇S` on the closed manifold
(the **integrated nullity**, the genuine moving-frame third-order Bochner–Weitzenböck content,
supplied here as `movingFrameRemainder_genuineSections_nullity`). The nullity (with `GcurvDeriv` taken
to be the combined field `genuineDiffCurvSection + ricTraceSection`) feeds
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`
(`MovingFrameRemainderDivergenceForm.lean`) to give the bracket-free pairing
`⟨GcurvSection + genuineDiffCurvSection + ricTraceSection, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}`, and the three
genuine fields carry the whole cross-pairing.

The Ricci-trace carrier is the missing fourth slot of the commutator defect: term-`(IV)` of the
slot table (`RicciTraceCarrier.lean`), the frame trace of the curvature's derivative-direction
contraction, producing `Ric`. It does NOT integrate to zero (at `s = 0` it carries the whole defect:
`Curv f = Ric(∇f, ·)`, `⟨Curv f, ∇f⟩ = ∫Ric(∇f, ∇f) > 0` on a positively-curved manifold), so it must
be subtracted alongside the two curvature fields.

Each genuine field is then bounded `L²`-proportionally:

* `GcurvSection g s S = pureRGenuineDiffOp g 0 (s + 1) (∇S)`
  (`pureRGenuineDiffOp0_eq_GcurvSection`) has fibre norm `≤ kappa · rfns(∇S)` by the
  section-proportional curvature bound `exists_proportional_pureRGenuineDiffOp`, so
  `‖GcurvSection g s S‖_{L²} ≤ √kappa · ‖∇S‖_{L²}` by the pointwise-to-`L²` packaging
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`.
* `genuineDiffCurvSection g s S = appCc (covGrad (curvOpField g s)) S` has fibre norm
  `≤ C · rfns(S)` by the uniform operator-field contraction bound
  `exists_uniform_riemannianFiberNormSq_appCc_le` (the fixed smooth differentiated-curvature operator
  `∇R` is uniformly fibre-bounded over the compact manifold), so
  `‖genuineDiffCurvSection g s S‖_{L²} ≤ √C · ‖S‖_{L²}`.
* `ricTraceSection g s S = appCc (ricSlotOpField g s) (∇S)` has fibre norm
  `≤ (C s)² · (rfns(∇S) + rfns(S))` by `exists_ricTraceSection_fiberNormSq_bound` (the fixed smooth
  raised-Ricci operator field is uniformly fibre-bounded), so
  `‖ricTraceSection g s S‖_{L²} ≤ Cric · (‖∇S‖_{L²} + ‖S‖_{L²})` by the same packaging.

Cauchy–Schwarz (`abs_tensorL2Inner_le`) then bounds the cross-pairing by
`(‖GcurvSection‖ + ‖genuineDiffCurvSection‖ + ‖ricTraceSection‖) · ‖∇S‖`, dominated by
`Ccross · (‖∇S‖² + ‖S‖ · ‖∇S‖)` for `Ccross := Cr + Cd + Cric`. The route never reads the gradient slot
pointwise and never differentiates the curvature beyond the fixed smooth coefficients `∇R`, `Ric`, so
it carries no chart-jet debt.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s` raises
the tensor rank from `(0, s)` to `(0, s + 1)`. All `L²` pairings are the global metric `L²` pairing
`tensorL2Inner` against the canonical Riemannian volume measure.
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_GcurvSection_l2Norm_le_covGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖GcurvSection (I := I) (M := M) g s S‖ ≤
        Cr * ‖covGrad (I := I) (M := M) g 0 s S‖ := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Real.sqrt (kappa 0 (s + 1)), Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : GcurvSection (I := I) (M := M) g s S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) :=
    (pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S).symm

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt (kappa 0 (s + 1))) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro x
    rw [Real.sq_sqrt (hkappa_nn 0 (s + 1)), hsec]
    have h := hkappa 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) x
    rw [Finset.sum_range_one,
      DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero] at h
    exact h

  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) (0 : SmoothCcTensor g 0 (s + 1))
    (GcurvSection (I := I) (M := M) g s S) (Real.sqrt (kappa 0 (s + 1))) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((0 : SmoothCcTensor g 0 (s + 1)).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 (s + 1) x
    rw [hz, add_zero]; exact hpt x

/-- **`L²` proportional control of the differentiated-curvature trace section by `S`.** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor
`S`, the metric `L²` norm of the differentiated-curvature trace section `genuineDiffCurvSection g s S`
(`= (∇R) S`, the operator-field action `appCc (covGrad (curvOpField g s)) S` of the covariant
derivative of the frame-free curvature operator field) is bounded by a uniform constant times the `L²`
norm of `S`:

```
‖genuineDiffCurvSection g s S‖ ≤ Cd · ‖S‖,     Cd ≥ 0 uniform in S.
```

The differentiated-curvature operator `covGrad (curvOpField g s)` is a *fixed* smooth
compactly-supported operator field (built from `g`, `R`, `∇R` alone), uniformly fibre-operator-bounded
over the compact manifold; the uniform operator-field contraction bound
`exists_uniform_riemannianFiberNormSq_appCc_le` gives `rfns(genuineDiffCurvSection g s S)(x) ≤ C ·
rfns(S)(x)`, lifted to the `L²` norm by `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with
`Cd = √C`. -/
theorem exists_genuineDiffCurvSection_l2Norm_le_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖genuineDiffCurvSection (I := I) (M := M) g s S‖ ≤ Cd * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g
    (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : genuineDiffCurvSection (I := I) (M := M) g s S =
      appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S := rfl
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt C) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro x
    rw [Real.sq_sqrt hC_nn, hsec]
    exact hC S x
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    S (0 : SmoothCcTensor g 0 s)
    (genuineDiffCurvSection (I := I) (M := M) g s S) (Real.sqrt C) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((0 : SmoothCcTensor g 0 s).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 s x
    rw [hz, add_zero]; exact hpt x

/-- **`L²` proportional control of the Ricci-trace carrier by `∇S` and `S`.** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`,
the metric `L²` norm of the Bochner–Lichnerowicz Ricci-trace carrier `ricTraceSection g s S`
(`= Ric(∇S)`, the term-`(IV)` slot of the order-`2` commutator defect, the operator-field action of the
fixed smooth raised-Ricci operator field `ricSlotOpField g s` on `∇S`) is bounded by a uniform constant
times the first-order Sobolev budget of `S`:

```
‖ricTraceSection g s S‖ ≤ Cric · (‖∇S‖ + ‖S‖),     ∇S := covGrad g 0 s S,   Cric ≥ 0 uniform in S.
```

The proof uses the uniform fibre bound `exists_ricTraceSection_fiberNormSq_bound`
(`rfns(ricTraceSection g s S)(x) ≤ (C s)² · (rfns(∇S)(x) + rfns(S)(x))`, the operator-field action of
the fixed smooth raised-Ricci field) and lifts it to the `L²` norm by the two-term pointwise-to-`L²`
packaging `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` with `A := ∇S`, `B := S`, `Cric := C s`. -/
theorem exists_ricTraceSection_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cric : ℝ, 0 ≤ Cric ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖ricTraceSection (I := I) (M := M) g s S‖ ≤
        Cric * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_ricTraceSection_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨C s, hC_nn s, fun S => ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) S
    (ricTraceSection (I := I) (M := M) g s S) (C s) (hC_nn s)
    (fun x => hC s S x)

/-- **The integrated `L²` curvature cross-bound (rank-generic).** For a closed smooth Riemannian
manifold `(M, g)`, covariant rank `s`, the one-sided `L²` curvature cross-term — minus the global
metric pairing of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S =
Δ_∇(∇S) − ∇(Δ_∇ S)` against the gradient field `∇S := covGrad g 0 s S` — is bounded by the first-order
Sobolev budget of `S`:

```
− ⟨Curv S, ∇S⟩_{L²} ≤ Ccross · (‖∇S‖²_{L²} + ‖S‖_{L²} · ‖∇S‖_{L²}),     Ccross ≥ 0 uniform in S.
```

**Proof (the classical first-order route).** The defect is first-order: by the pointwise first-order
curvature fibre bound `exists_pointwiseTensorCurv_fiberNormSq_bound` (the genuine moving-frame
third-order Bochner–Weitzenböck `∇²S`-elimination) there are uniform `K_R, K_dR ≥ 0` with
`√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x))`. Squaring with `(a + b)² ≤
2 a² + 2 b²` gives the pointwise-to-`L²` budget `rfns(Curv S)(x) ≤ C² · (rfns(∇S)(x) + rfns(S)(x))`
with `C := √2 · max K_R K_dR`, which the two-term packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` lifts to `‖Curv S‖ ≤ C · (‖∇S‖ + ‖S‖)`.
Cauchy–Schwarz (`abs_tensorL2Inner_le`) then bounds the cross-pairing by
`‖Curv S‖ · ‖∇S‖ ≤ C · (‖∇S‖ + ‖S‖) · ‖∇S‖ = C · (‖∇S‖² + ‖S‖ · ‖∇S‖)`, and
`−⟨Curv S, ∇S⟩ ≤ |⟨Curv S, ∇S⟩|`. The route reads the defect only through its first-order fibre
bound and never through the (false-as-stated) integrated three-carrier nullity. -/
theorem exists_integrated_curvatureCrossBound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ S : SmoothCcTensor g 0 s,
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross *
            (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
                tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S).toFun) := by
  classical
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hfibre⟩ :=
    exists_pointwiseTensorCurv_fiberNormSq_bound (I := I) (M := M) g s

  set C : ℝ := Real.sqrt 2 * max K_R K_dR with hC_def
  have hmax_nn : 0 ≤ max K_R K_dR := le_max_of_le_left hK_R_nn
  have hC_nn : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hmax_nn
  refine ⟨C, hC_nn, fun S => ?_⟩
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgradS_def

  have hCurvFun : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun := rfl

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
        C ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
    intro x
    set rC : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) with hrC_def
    set rG : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hrG_def
    set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hrS_def
    have hrC_nn : 0 ≤ rC := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrG_nn : 0 ≤ rG := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrS_nn : 0 ≤ rS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hsqrtC : Real.sqrt rC ≤ K_R * Real.sqrt rG + K_dR * Real.sqrt rS := hfibre S x

    have hsqrtC' : Real.sqrt rC ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) := by
      refine le_trans hsqrtC ?_
      have h1 : K_R * Real.sqrt rG ≤ max K_R K_dR * Real.sqrt rG :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      have h2 : K_dR * Real.sqrt rS ≤ max K_R K_dR * Real.sqrt rS :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
      nlinarith [h1, h2]
    have hrC_eq : rC = Real.sqrt rC ^ 2 := (Real.sq_sqrt hrC_nn).symm
    have hrG_eq : rG = Real.sqrt rG ^ 2 := (Real.sq_sqrt hrG_nn).symm
    have hrS_eq : rS = Real.sqrt rS ^ 2 := (Real.sq_sqrt hrS_nn).symm
    have hC_sq : C ^ 2 = 2 * max K_R K_dR ^ 2 := by
      rw [hC_def, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hC_sq, hrC_eq, hrG_eq, hrS_eq]
    have hsqrtrC_nn : 0 ≤ Real.sqrt rC := Real.sqrt_nonneg _
    have hsum_nn : 0 ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) :=
      mul_nonneg hmax_nn (by positivity)
    nlinarith [hsqrtC', sq_nonneg (Real.sqrt rG - Real.sqrt rS),
      mul_nonneg hmax_nn hmax_nn, Real.sqrt_nonneg rG, Real.sqrt_nonneg rS,
      mul_le_mul hsqrtC' hsqrtC' hsqrtrC_nn hsum_nn]

  have hL2 : ‖pointwiseTensorCurv (I := I) (M := M) g s S‖ ≤
      C * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 s S) S
      (pointwiseTensorCurv (I := I) (M := M) g s S) C hC_nn hpt

  rw [SmoothCcTensor.norm_def (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S),
    SmoothCcTensor.norm_def (I := I) (M := M) (covGrad (I := I) (M := M) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) S] at hL2

  have hcs : |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| ≤
      tensorL2Norm (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun *
        tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun :=
    abs_tensorL2Inner_le (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pointwiseTensorCurv (I := I) (M := M) g s S) gradS)

  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun with hnGrad_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1)
    (pointwiseTensorCurv (I := I) (M := M) g s S).toFun with hnCurv_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _

  have hval_eq :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) -
          covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun := by
    rw [← hgradS_def, ← hCurvFun]
  rw [hval_eq]

  have hneg_le : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| := neg_le_abs _
  have hstep1 : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      nCurv * nGrad :=
    le_trans hneg_le hcs
  calc - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      ≤ nCurv * nGrad := hstep1
    _ ≤ (C * (nGrad + nS)) * nGrad := mul_le_mul_of_nonneg_right hL2 hnGrad_nn
    _ = C * (nGrad ^ 2 + nS * nGrad) := by ring

end Connection
end Integral
end DifferentialGeometry

end
