import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePartnerBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MovingEdgeEnergy

/-!
# Ricci--DeTurck rate bound at the closed initial edge

This file assembles the fixed-time analytic estimate behind the moving
difference energy.  The top nonlinear coefficient is never differentiated as
an opaque coefficient.  Instead the Palatini--DeTurck refold exposes its
formal partner, whose zeroth and first covariant derivatives both retain the
small metric-difference factor.

The principal estimate is applied to `s • W`, because the metric at slope
parameter `s` is `g + s W`.  Dividing the resulting quadratic inequality by
`s ^ 2` is essential; applying the principal theorem directly to `W` would
use the wrong realization identity.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## A refold normal form which retains the formal-partner data -/

/-- The complete order-zero field left after the top refold. -/
def edgeRate0 (g gm g_bg : SmoothRiemannianMetric I M)
    (C0 : SmoothCcTensor g 2 2) : SmoothCcTensor g 2 2 :=
  edgeCarry0 (I := I) (M := M) g g_bg +
    (-2 : Real) • edgeRicciHalf (I := I) (M := M) g gm + C0 +
    edgeFold0 (I := I) (M := M) g gm g_bg

/-- The complete order-one field left after the top refold. -/
def edgeRate1 (g gm g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  edgeCarry1 (I := I) (M := M) g g_bg +
    edgeQuad1 (I := I) (M := M) g gm g_bg

/-- Closed-edge slope refold retaining the permutations and signs which define
the formal top partner.

Unlike `exists_edgeSlopeRef`, this theorem deliberately returns `qA`, `qB`,
`q`, and `epsilon`.  They are required by `edgeTop_zero` and `edgeTop_one`, so
hiding them behind an existential coefficient would make the sharp top-order
energy estimate impossible to consume. -/
theorem exists_edgePairRef
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g W x v w = ccTensorBilin (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) delta) :
    ∃ B0 : Real, 0 ≤ B0 ∧
      ∃ (C0 : Real → SmoothCcTensor g 2 2)
        (qA qB : Fin 4 → Equiv.Perm (Fin 4))
        (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
        (∀ i, |epsilon i| ≤ 1) ∧
        (∀ s ∈ Set.Icc (0 : Real) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((C0 s).toSection x) ≤ B0 ^ 2) ∧
        ∀ (x : M) (v w : TangentSpace I x) {s : Real},
          s ∈ Set.Ioo (0 : Real) 1 →
          DeTurckCoefficients.rhsSumSlope (I := I) g g_bg W 0
              (lt_of_le_of_lt hdelta_half (by norm_num : (1 / 2 : Real) < 1))
              hdelta (show (0 : Real) < 1 by norm_num)
              (edgeZeroBound (I := I) (M := M) g) x v w s =
            unitModel (I := I) (M := M) g 2
              (edgeCoreArm (I := I) (M := M) g
                  (edgeMetric (I := I) (M := M) g W hdelta s)
                  (edgeRate0 (I := I) (M := M) g
                    (edgeMetric (I := I) (M := M) g W hdelta s) g_bg (C0 s))
                  (edgeRate1 (I := I) (M := M) g
                    (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
                appCc (I := I) (M := M) g 2 2
                  (edgeTopPair (I := I) (M := M) g W hdelta
                    (edgeZeroBoundAt (I := I) (M := M) g hdelta_nn)
                    qA qB q epsilon s) W) x ![v, w] := by
  classical
  let a : Nat := 2 * Module.finrank Real E + 10
  let R : Real := ∑ j ∈ Finset.range (a + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j W‖
  have ha : 2 * Module.finrank Real E + 10 ≤ a := by rfl
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hball : ∀ j : Nat, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g 0 2 j W‖ ≤ R := by
    intro j hj
    exact Finset.single_le_sum
      (f := fun k => ‖iteratedCovGrad (I := I) g 0 2 k W‖)
      (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hhalf_lt : (1 / 2 : Real) < 1 := by norm_num
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_half hhalf_lt
  let hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta :=
    edgeZeroBoundAt (I := I) (M := M) g hdelta_nn
  obtain ⟨LambdaR, hLambdaR, KR, hKR, qA, qB, hq, hRmain⟩ :=
    exists_riemannPalatini_refold_identity_data (I := I) (M := M)
      g a ha hR hhalf_lt
  obtain ⟨LambdaD, hLambdaD, KD, hKD, q, epsilon, hepsilon, hDmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M)
      g g_bg a ha hR hhalf_lt
  obtain ⟨C0R, hjR, hidR, hsupR, henvR⟩ :=
    hRmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨C0D, hjD, hidD, hsupD, henvD⟩ :=
    hDmain W hWsymm hdelta_half hdelta hdeltaZ hball
  let C0 : Real → SmoothCcTensor g 2 2 := fun s => C0R s + C0D s
  let C2 : Real → SmoothCcTensor g 4 2 := fun s =>
    (2 : Real) •
        riemannPalatiniRefoldC2Family (I := I) (M := M)
          g W hdelta hdeltaZ qA qB s +
      deTurckLieCovDerivRefoldC2Family (I := I) (M := M)
        g W hdelta hdeltaZ q epsilon s
  have hquad : ∀ s ∈ Set.Icc (0 : Real) 1,
      edgeQuadArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W =
        (-2 : Real) • appCc (I := I) (M := M) g 2 2
            (edgeRicciHalf (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s)) W +
          appCc (I := I) (M := M) g 2 2 (C0 s) W +
          appCc (I := I) (M := M) g 2 2
            (edgeFold0 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
          appCc (I := I) (M := M) g 3 2
            (edgeQuad1 (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) g_bg)
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          appCc (I := I) (M := M) g 4 2 (C2 s)
            (iteratedCovGrad (I := I) g 0 2 2 W) := by
    intro s hs
    have hmetric := edgeMetric_bal (I := I) (M := M)
      g W hdelta_lt hdelta hdeltaZ hs
    have hriem := hidR s hs
    have hlie := hidD s hs
    simp only [iteratedCovGrad_zero] at hriem hlie
    rw [hmetric]
    simp only [edgeQuadArm, edgeLowerArm, edgeQuad0,
      deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      appCc_add_left, appCc_sub_left, appCc_smul_left]
    rw [hriem, hlie]
    simp only [edgeRicciHalf, edgeFold0, C0, C2,
      appCc_add_left, appCc_sub_left, appCc_smul_left]
    module
  have htop : ∀ s : Real,
      appCc (I := I) (M := M) g 4 2 (C2 s)
          (iteratedCovGrad (I := I) g 0 2 2 W) =
        appCc (I := I) (M := M) g 2 2
          (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W := by
    intro s
    simpa only [C2] using
      (edgeTopPair_apply (I := I) (M := M) g W hdelta hdeltaZ
        qA qB q epsilon s).symm
  have hnormal : ∀ s ∈ Set.Icc (0 : Real) 1,
      (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hdelta s) W) +
        (edgeCarryArm (I := I) (M := M) g g_bg W +
          edgeQuadArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hdelta s) g_bg W) =
      edgeCoreArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s)
          (edgeRate0 (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hdelta s) g_bg (C0 s))
          (edgeRate1 (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hdelta s) g_bg) W +
        appCc (I := I) (M := M) g 2 2
          (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W := by
    intro s hs
    rw [hquad s hs, htop s]
    simp only [edgeCoreArm, edgeLowerArm, edgeCarryArm,
      edgeRate0, edgeRate1, appCc_add_left, appCc_smul_left]
    module
  have hBsq : 0 ≤ 2 * LambdaR ^ 2 + 2 * LambdaD ^ 2 := by positivity
  let B0 : Real := Real.sqrt (2 * LambdaR ^ 2 + 2 * LambdaD ^ 2)
  refine ⟨B0, Real.sqrt_nonneg _, C0, qA, qB, q, epsilon, hepsilon, ?_, ?_⟩
  · intro s hs x
    dsimp only [C0, B0]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 2 2 x ((C0R s).toSection x) ((C0D s).toSection x)
    have hR0 := hsupR s hs x
    have hD0 := hsupD s hs x
    rw [Real.sq_sqrt hBsq]
    linarith
  · intro x v w s hs
    have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hslope := edgeSlope_split (I := I) (M := M)
      g g_bg W hWsymm hdelta_lt hdelta x v w hs
    rw [hslope, hnormal s hscc]

/-! ## Principal absorption on the genuine slope segment -/

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem edge_unit_smul
    (g : SmoothRiemannianMetric I M) (c : Real)
    (A : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (c • A) x v =
      c * unitModel (I := I) (M := M) g 2 A x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (c • A) x =
      c • unitModel (I := I) (M := M) g 2 A x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smul_apply,
      Tensor0SSpace.toModel_smul]
  rw [hfun, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

private theorem edge_lap_smul
    (g : SmoothRiemannianMetric I M) (c : Real)
    (W : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 2 (c • W) =
      c • rawTensorConnLapSmooth (I := I) g 0 2 W := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
      (I := I) (M := M) g (c • W) x v,
    edge_unit_smul (I := I) (M := M) g c
      (rawTensorConnLapSmooth (I := I) g 0 2 W) x v,
    rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
      (I := I) (M := M) g W x v,
    iteratedCovGrad_smul, appCc_smul_right,
    edge_unit_smul (I := I) (M := M) g c
      (appCc (I := I) (M := M) g 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 W)) x v]

private theorem edge_core_smul
    (g gm : SmoothRiemannianMetric I M)
    (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
    (c : Real) (W : SmoothCcTensor g 0 2) :
    edgeCoreArm (I := I) (M := M) g gm C0 C1 (c • W) =
      c • edgeCoreArm (I := I) (M := M) g gm C0 C1 W := by
  simp only [edgeCoreArm, edgeLowerArm, deTurckPrincipalCometricArm,
    edge_lap_smul, iteratedCovGrad_smul, appCc_smul_right]
  module

private lemma edge_bound_mono
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {a b : Real} (hab : a ≤ b)
    (ha : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) a) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) b := by
  intro x v w
  exact (ha x v w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-- Principal and lower-order absorption at a genuine slope parameter.

The realization identity for `edgeMetric g W hdelta s` is tied to `s • W`.
Accordingly the proof applies `edgeCore_pair_le` to that scaled tensor and
then cancels the positive factor `s ^ 2`. -/
theorem edgeCore_path_le [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g W x v w =
            ccTensorBilin (I := I) g W x w v)
        {B0 B1 delta s : Real},
        0 ≤ B0 → 0 ≤ B1 → delta < 1 / 2 → 0 ≤ delta →
        (hWbound : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        delta / (1 - delta) + C * delta ≤ 1 / 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            (C0.toSection x) ≤ B0 ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (C1.toSection x) ≤ B1 ^ 2) →
        s ∈ Set.Ioo (0 : Real) 1 →
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (edgeCoreArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W
                hWbound s) C0 C1 W).toFun ≤
          -(1 / 4 : Real) *
              ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
            (B0 + B1 ^ 2) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hcore⟩ := edgeCore_pair_le (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro C0 C1 W hWsymm B0 B1 delta s hB0 hB1 hdelta hdelta0
    hWbound hsmall hC0 hC1 hs
  let P : SmoothCcTensor g 0 2 := s • W
  let gm : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g W hWbound s
  have hdelta_lt : delta < 1 := lt_trans hdelta (by norm_num)
  have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hsSmall : s ∈ realizedSmallSet (δ := delta) (δ' := 0) :=
    Icc_subset_realizedSmallSet hdelta_lt (by norm_num) hscc
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    have hpath := realizedFam_inner_of_mem (I := I) (M := M)
      g W 0 hWbound (edgeZeroBound (I := I) (M := M) g)
      hsSmall y v w
    simpa only [gm, edgeMetric, P, convexPerturbation, smul_zero,
      zero_add] using hpath
  have hPraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s W hWbound
  have hsabs : |s| ≤ 1 := by
    rw [abs_of_pos hs.1]
    exact hs.2.le
  have hrad : |s| * delta ≤ delta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsabs) hdelta0]
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta :=
    edge_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hWfix : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g W hWsymm
  have hPfix : symmS (I := I) (M := M) g P = P := by
    simp only [P, symmS_smul, hWfix]
  have hp := hcore gm C0 C1 P hB0 hB1 hdelta hdelta0
    htie hPbound hPfix hsmall hC0 hC1
  have hcoreSmul :
      edgeCoreArm (I := I) (M := M) g gm C0 C1 P =
        s • edgeCoreArm (I := I) (M := M) g gm C0 C1 W := by
    simpa only [P] using
      edge_core_smul (I := I) (M := M) g gm C0 C1 s W
  have hpair :
      tensorL2Inner (I := I) (M := M) g 0 2 P.toFun
          (edgeCoreArm (I := I) (M := M) g gm C0 C1 P).toFun =
        s ^ 2 * tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (edgeCoreArm (I := I) (M := M) g gm C0 C1 W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) P
      (edgeCoreArm (I := I) (M := M) g gm C0 C1 P),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (edgeCoreArm (I := I) (M := M) g gm C0 C1 W),
      hcoreSmul]
    simp only [P, real_inner_smul_left, real_inner_smul_right]
    ring
  have hgrad :
      ‖iteratedCovGrad (I := I) g 0 2 1 P‖ =
        s * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ := by
    simp only [P, iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs.1]
  have hnorm : ‖P‖ = s * ‖W‖ := by
    simp only [P, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
  rw [hpair, hgrad, hnorm] at hp
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs.1
  change tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
      (edgeCoreArm (I := I) (M := M) g gm C0 C1 W).toFun ≤ _
  nlinarith

/-! ## Formal-partner absorption -/

private theorem edge_l2_of_rfns
    (g : SmoothRiemannianMetric I M) (ra sa rb sb : Nat)
    (A : SmoothCcTensor g ra sa) (B : SmoothCcTensor g rb sb)
    {c : Real} (hc : 0 ≤ c)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g ra sa x
          (A.toSection x) ≤
        c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g rb sb x
          (B.toSection x)) :
    ‖A‖ ≤ c * ‖B‖ := by
  have hint : Integrable
      (fun x => c ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g rb sb x
          (B.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g rb sb B).const_mul (c ^ 2)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g ra sa A _ hint hpt
  rw [integral_const_mul,
    ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g rb sb B,
    DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm]
    at hsq
  have hright : 0 ≤ c * ‖B‖ := mul_nonneg hc (norm_nonneg B)
  nlinarith [norm_nonneg A]

/-- The complete top refold pairing is absorbed by one quarter of the
Dirichlet energy on a radius chosen from the carrier metric alone.  The
remaining coefficient multiplies only the `L²` energy of `W`. -/
theorem edgeTop_pair_le
    (g : SmoothRiemannianMetric I M) :
    ∃ delta0 K : Real, 0 < delta0 ∧ delta0 < 1 / 2 ∧ 0 ≤ K ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g W x v w =
            ccTensorBilin (I := I) g W x w v)
        {delta : Real}, 0 ≤ delta → delta ≤ delta0 →
        (hdelta : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        (hdeltaZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) delta) →
        ∀ (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ s ∈ Set.Icc (0 : Real) 1,
            (⟪W, appCc (I := I) (M := M) g 2 2
              (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
                qA qB q epsilon s) W⟫_Real : Real) ≤
              (1 / 4 : Real) *
                  ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
                K * ‖W‖ ^ 2 := by
  classical
  obtain ⟨C0, hC0, hzero⟩ := edgeTop_zero (I := I) (M := M) g
  obtain ⟨C1, hC1, hone⟩ := edgeTop_one (I := I) (M := M) g
  obtain ⟨Kd, hKd, hdiv⟩ :=
    exists_iteratedCovGrad_covDivergence_l2_le
      (I := I) (M := M) g 3
  let A : Real := Kd 0 * Real.sqrt C0
  let B : Real := Kd 0 * Real.sqrt C1
  have hA : 0 ≤ A := mul_nonneg (hKd 0) (Real.sqrt_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (hKd 0) (Real.sqrt_nonneg _)
  let delta0 : Real := 1 / (8 * (1 + B))
  let K : Real := 2 * A ^ 2
  have hden : 0 < 8 * (1 + B) := by positivity
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact one_div_pos.mpr hden
  have hdelta0_half : delta0 < 1 / 2 := by
    dsimp only [delta0]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨delta0, K, hdelta0, hdelta0_half, hK, ?_⟩
  intro W hWsymm delta hdelta0' hdelta_cap hdelta hdeltaZ
    qA qB q epsilon hepsilon s hs
  have hdelta_half : delta ≤ 1 / 2 := hdelta_cap.trans hdelta0_half.le
  let P : SmoothCcTensor g 0 4 :=
    edgeTopPartner (I := I) (M := M) g W hdelta hdeltaZ
      qA qB q epsilon s
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  have hP : ‖P‖ ≤ Real.sqrt C0 * delta * ‖W‖ := by
    apply edge_l2_of_rfns (I := I) (M := M) g 0 4 0 2 P W
      (mul_nonneg (Real.sqrt_nonneg _) hdelta0')
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 4 x
          (P.toSection x) ≤
          C0 * delta ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (W.toSection x) := by
        simpa only [P] using
          hzero W hWsymm hdelta0' hdelta_half hdelta hdeltaZ
            qA qB q epsilon hepsilon s hs x
      _ = (Real.sqrt C0 * delta) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (W.toSection x) := by
        rw [mul_pow, Real.sq_sqrt hC0]
  have hP1 : ‖covGrad (I := I) (M := M) g 0 4 P‖ ≤
      Real.sqrt C1 * delta * ‖D‖ := by
    apply edge_l2_of_rfns (I := I) (M := M) g 0 5 0 3
      (covGrad (I := I) (M := M) g 0 4 P) D
      (mul_nonneg (Real.sqrt_nonneg _) hdelta0')
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 5 x
          ((covGrad (I := I) (M := M) g 0 4 P).toSection x) ≤
          C1 * delta ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              (D.toSection x) := by
        simpa only [P, D] using
          hone W hWsymm hdelta0' hdelta_half hdelta hdeltaZ
            qA qB q epsilon hepsilon s hs x
      _ = (Real.sqrt C1 * delta) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              (D.toSection x) := by
        rw [mul_pow, Real.sq_sqrt hC1]
  have hsum :
      (∑ k ∈ Finset.range (0 + 2),
          ‖iteratedCovGrad (I := I) g 0 4 k P‖) =
        ‖P‖ + ‖covGrad (I := I) (M := M) g 0 4 P‖ := by
    norm_num [Finset.sum_range_succ]
  have hdiv0 :
      ‖covDivergence (I := I) (M := M) g 3 P‖ ≤
        Kd 0 * (‖P‖ + ‖covGrad (I := I) (M := M) g 0 4 P‖) := by
    have h := hdiv 0 P
    simp only [iteratedCovGrad_zero] at h
    rw [hsum] at h
    exact h
  have hdiv1 :
      ‖covDivergence (I := I) (M := M) g 3 P‖ ≤
        A * delta * ‖W‖ + B * delta * ‖D‖ := by
    calc
      ‖covDivergence (I := I) (M := M) g 3 P‖ ≤
          Kd 0 * (‖P‖ + ‖covGrad (I := I) (M := M) g 0 4 P‖) := hdiv0
      _ ≤ Kd 0 * ((Real.sqrt C0 * delta * ‖W‖) +
          (Real.sqrt C1 * delta * ‖D‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hP hP1) (hKd 0)
      _ = A * delta * ‖W‖ + B * delta * ‖D‖ := by
        dsimp only [A, B]
        ring
  have hpair :
      (⟪W, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W⟫_Real : Real) ≤
        (A * delta * ‖W‖ + B * delta * ‖D‖) * ‖D‖ := by
    calc
      (⟪W, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W⟫_Real : Real) =
          -⟪covDivergence (I := I) (M := M) g 3 P, D⟫_Real := by
        simpa only [P, D] using
          edgeTop_green (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s
      _ ≤ |⟪covDivergence (I := I) (M := M) g 3 P, D⟫_Real| := by
        exact neg_le_abs _
      _ ≤ ‖covDivergence (I := I) (M := M) g 3 P‖ * ‖D‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (A * delta * ‖W‖ + B * delta * ‖D‖) * ‖D‖ :=
        mul_le_mul_of_nonneg_right hdiv1 (norm_nonneg D)
  have hBdelta : B * delta ≤ 1 / 8 := by
    calc
      B * delta ≤ B * delta0 :=
        mul_le_mul_of_nonneg_left hdelta_cap hB
      _ = B / (8 * (1 + B)) := by
        dsimp only [delta0]
        ring
      _ ≤ 1 / 8 := by
        apply (div_le_iff₀ hden).2
        nlinarith
  have hdelta_sq : delta ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (delta - 1)]
  have hcross : A * delta * ‖W‖ * ‖D‖ ≤
      (1 / 8 : Real) * ‖D‖ ^ 2 +
        2 * A ^ 2 * delta ^ 2 * ‖W‖ ^ 2 := by
    nlinarith [sq_nonneg (‖D‖ - 4 * (A * delta * ‖W‖))]
  have hgrad : B * delta * ‖D‖ ^ 2 ≤
      (1 / 8 : Real) * ‖D‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hBdelta (sq_nonneg ‖D‖)
  have hzeroTerm : 2 * A ^ 2 * delta ^ 2 * ‖W‖ ^ 2 ≤
      K * ‖W‖ ^ 2 := by
    dsimp only [K]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdelta_sq (by positivity))
      (sq_nonneg ‖W‖)
  dsimp only [D] at hpair hcross hgrad ⊢
  calc
    (⟪W, appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W⟫_Real : Real) ≤
        (A * delta * ‖W‖ + B * delta *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ := hpair
    _ = A * delta * ‖W‖ * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ +
        B * delta * ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 := by ring
    _ ≤ ((1 / 8 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        2 * A ^ 2 * delta ^ 2 * ‖W‖ ^ 2) +
          (1 / 8 : Real) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 :=
      add_le_add hcross hgrad
    _ ≤ (1 / 4 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        K * ‖W‖ ^ 2 := by linarith

/-! ## Fixed-time slope pairing -/

/-- Conditional fixed-time pairing estimate once the supplied lower
coefficient fields have pointwise bounds.  This is generic refold glue, not
the missing bound producer for the concrete `edgeRate0` and `edgeRate1`.
The negative quarter from the principal/lower arm cancels the positive
quarter used to absorb the formal top partner. -/
theorem edgePair_pair_le [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C delta0 K : Real,
      0 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 / 2 ∧ 0 ≤ K ∧
      ∀ (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2)
        (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g W x v w =
            ccTensorBilin (I := I) g W x w v)
        {B0 B1 delta s : Real},
        0 ≤ B0 → 0 ≤ B1 → 0 ≤ delta → delta ≤ delta0 →
        (hdelta : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        (hdeltaZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) delta) →
        delta / (1 - delta) + C * delta ≤ 1 / 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            (C0.toSection x) ≤ B0 ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (C1.toSection x) ≤ B1 ^ 2) →
        (qA qB : Fin 4 → Equiv.Perm (Fin 4)) →
        (q : Fin 3 → Equiv.Perm (Fin 4)) → (epsilon : Fin 3 → Real) →
        (∀ i, |epsilon i| ≤ 1) → s ∈ Set.Ioo (0 : Real) 1 →
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (edgeCoreArm (I := I) (M := M) g
                (edgeMetric (I := I) (M := M) g W hdelta s) C0 C1 W +
              appCc (I := I) (M := M) g 2 2
                (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
                  qA qB q epsilon s) W).toFun ≤
          (B0 + B1 ^ 2 + K) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hcore⟩ := edgeCore_path_le (I := I) (M := M) g
  obtain ⟨delta0, K, hdelta0, hdelta0_half, hK, htop⟩ :=
    edgeTop_pair_le (I := I) (M := M) g
  refine ⟨C, delta0, K, hC, hdelta0, hdelta0_half, hK, ?_⟩
  intro C0 C1 W hWsymm B0 B1 delta s hB0 hB1 hdelta0'
    hdelta_cap hdelta hdeltaZ hsmall hC0 hC1 qA qB q epsilon hepsilon hs
  have hdelta_half : delta < 1 / 2 :=
    lt_of_le_of_lt hdelta_cap hdelta0_half
  have hcore0 := hcore C0 C1 W hWsymm hB0 hB1 hdelta_half
    hdelta0' hdelta hsmall hC0 hC1 hs
  have htop0 := htop W hWsymm hdelta0' hdelta_cap hdelta hdeltaZ
    qA qB q epsilon hepsilon s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have htop1 :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (appCc (I := I) (M := M) g 2 2
            (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
              qA qB q epsilon s) W).toFun ≤
        (1 / 4 : Real) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
          K * ‖W‖ ^ 2 := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W)]
    exact htop0
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (edgeCoreArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hdelta s) C0 C1 W +
            appCc (I := I) (M := M) g 2 2
              (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
                qA qB q epsilon s) W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (edgeCoreArm (I := I) (M := M) g
            (edgeMetric (I := I) (M := M) g W hdelta s) C0 C1 W).toFun +
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (appCc (I := I) (M := M) g 2 2
            (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
              qA qB q epsilon s) W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (edgeCoreArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s) C0 C1 W +
        appCc (I := I) (M := M) g 2 2
          (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (edgeCoreArm (I := I) (M := M) g
          (edgeMetric (I := I) (M := M) g W hdelta s) C0 C1 W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (appCc (I := I) (M := M) g 2 2
          (edgeTopPair (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W),
      real_inner_add_right]
  rw [hadd]
  nlinarith

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
