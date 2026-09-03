import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.AdjointBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MovingMetricDifferenceEnergy
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral


open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private local instance edgeRateTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

private local instance edgeRateTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

private local instance edgeRateTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

private local instance edgeRateTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

def ricciDeTurckPairingZeroOrderCoefficient (g gm g_bg : SmoothRiemannianMetric I M)
    (C0 : SmoothCcTensor g 2 2) : SmoothCcTensor g 2 2 :=
  backgroundZeroOrderCoefficient (I := I) (M := M) g g_bg +
    (-2 : Real) • ricciPalatiniHalfCoefficient (I := I) (M := M) g gm + C0 +
    ricciPalatiniZeroOrderFold (I := I) (M := M) g gm g_bg

def ricciDeTurckPairingFirstOrderCoefficient (g gm g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  backgroundFirstOrderCoefficient (I := I) (M := M) g g_bg +
    metricDependentFirstOrderCoefficient (I := I) (M := M) g gm g_bg

theorem exists_ricciDeTurck_pairing_coefficient_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {delta : Real} (hdelta_nn : 0 ≤ delta) (hdelta_half : delta ≤ 1 / 2)
    (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
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
              (zero_metricPerturbation_bound (I := I) (M := M) g) x v w s =
            unitModel (I := I) (M := M) g 2
              (ricciDeTurckLowOrderAction (I := I) (M := M) g
                  (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)
                  (ricciDeTurckPairingZeroOrderCoefficient (I := I) (M := M) g
                    (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg (C0 s))
                  (ricciDeTurckPairingFirstOrderCoefficient (I := I) (M := M) g
                    (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W +
                operatorFieldApply (I := I) (M := M) g 2 2
                  (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta
                    (metricPerturbation_zero_bound_at (I := I) (M := M) g hdelta_nn)
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
  let hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta :=
    metricPerturbation_zero_bound_at (I := I) (M := M) g hdelta_nn
  obtain ⟨LambdaR, hLambdaR, KR, hKR, qA, qB, hq, hRmain⟩ :=
    exists_riemannPalatini_decomposition_identity_data (I := I) (M := M)
      g a ha hR hhalf_lt
  obtain ⟨LambdaD, hLambdaD, KD, hKD, q, epsilon, hepsilon, hDmain⟩ :=
    exists_deTurckLieCovariantDerivativeArm_decomposition_identity_data (I := I) (M := M)
      g g_bg a ha hR hhalf_lt
  obtain ⟨C0R, hjR, hidR, hsupR, henvR⟩ :=
    hRmain W hWsymm hdelta_half hdelta hdeltaZ hball
  obtain ⟨C0D, hjD, hidD, hsupD, henvD⟩ :=
    hDmain W hWsymm hdelta_half hdelta hdeltaZ hball
  let C0 : Real → SmoothCcTensor g 2 2 := fun s => C0R s + C0D s
  let C2 : Real → SmoothCcTensor g 4 2 := fun s =>
    (2 : Real) •
        riemannPalatiniDecompositionC2Family (I := I) (M := M)
          g W hdelta hdeltaZ qA qB s +
      deTurckLieCovariantDerivativeDecompositionC2Family (I := I) (M := M)
        g W hdelta hdeltaZ q epsilon s
  have hquad : ∀ s ∈ Set.Icc (0 : Real) 1,
      metricDependentLowOrderAction (I := I) (M := M) g
          (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W =
        (-2 : Real) • operatorFieldApply (I := I) (M := M) g 2 2
            (ricciPalatiniHalfCoefficient (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)) W +
          operatorFieldApply (I := I) (M := M) g 2 2 (C0 s) W +
          operatorFieldApply (I := I) (M := M) g 2 2
            (ricciPalatiniZeroOrderFold (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W +
          operatorFieldApply (I := I) (M := M) g 3 2
            (metricDependentFirstOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg)
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          operatorFieldApply (I := I) (M := M) g 4 2 (C2 s)
            (iteratedCovGrad (I := I) g 0 2 2 W) := by
    intro s hs
    have hmetric := metricComparisonEndomorphism_pairing_balance (I := I) (M := M)
      g W hdelta_lt hdelta hdeltaZ hs
    have hriem := hidR s hs
    have hlie := hidD s hs
    simp only [iteratedCovGrad_zero] at hriem hlie
    rw [hmetric]
    simp only [metricDependentLowOrderAction, firstOrderCoefficientAction, metricDependentZeroOrderCoefficient,
      deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
      operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left]
    rw [hlie]
    simp only [ricciPalatiniHalfCoefficient, ricciPalatiniZeroOrderFold, C0, C2,
      operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left]
    rw [hriem]
    simp only [operatorFieldApplication_smul_left]
    module
  have htop : ∀ s : Real,
      operatorFieldApply (I := I) (M := M) g 4 2 (C2 s)
          (iteratedCovGrad (I := I) g 0 2 2 W) =
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W := by
    intro s
    simpa only [C2] using
      (ricciDeTurckTopOrderPairingCoefficient_apply (I := I) (M := M) g W hdelta hdeltaZ
        qA qB q epsilon s).symm
  have hnormal : ∀ s ∈ Set.Icc (0 : Real) 1,
      (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricArm (I := I) (M := M) g
            (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) W) +
        (backgroundLowOrderAction (I := I) (M := M) g g_bg W +
          metricDependentLowOrderAction (I := I) (M := M) g
            (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg W) =
      ricciDeTurckLowOrderAction (I := I) (M := M) g
          (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s)
          (ricciDeTurckPairingZeroOrderCoefficient (I := I) (M := M) g
            (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg (C0 s))
          (ricciDeTurckPairingFirstOrderCoefficient (I := I) (M := M) g
            (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) g_bg) W +
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W := by
    intro s hs
    rw [hquad s hs, htop s]
    simp only [ricciDeTurckLowOrderAction, firstOrderCoefficientAction, backgroundLowOrderAction,
      ricciDeTurckPairingZeroOrderCoefficient, ricciDeTurckPairingFirstOrderCoefficient, operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
    module
  have hBsq : 0 ≤ 2 * LambdaR ^ 2 + 2 * LambdaD ^ 2 := by positivity
  let B0 : Real := Real.sqrt (2 * LambdaR ^ 2 + 2 * LambdaD ^ 2)
  refine ⟨B0, Real.sqrt_nonneg _, C0, qA, qB, q, epsilon, hepsilon, ?_, ?_⟩
  · intro s hs x
    dsimp only [C0, B0]
    change riemannianFiberNormSq (I := I) (M := M) g 2 2 x
      ((C0R s).toSection x + (C0D s).toSection x) ≤ _
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 2 2 x ((C0R s).toSection x) ((C0D s).toSection x)
    have hR0 := hsupR s hs x
    have hD0 := hsupD s hs x
    rw [Real.sq_sqrt hBsq]
    linarith
  · intro x v w s hs
    have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hslope := ricciDeTurckRhsSlope_decomposition (I := I) (M := M)
      g g_bg W hWsymm hdelta_lt hdelta x v w hs
    rw [hslope, hnormal s hscc]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem edge_unit_smul
    (g : SmoothRiemannianMetric I M) (c : Real)
    (A : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (c • A) x v =
      c * unitModel (I := I) (M := M) g 2 A x v := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, smul_apply, smul_eq_mul]

omit [SigmaCompactSpace M] in
private theorem edge_lap_smul
    (g : SmoothRiemannianMetric I M) (c : Real)
    (W : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 2 (c • W) =
      c • rawTensorConnLapSmooth (I := I) g 0 2 W := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  let v' : Fin 2 → TangentSpace I x := fun j =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v j)
  have hleft :=
    rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace
      (I := I) (M := M) g (c • W) x v'
  have hright :=
    rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace
      (I := I) (M := M) g W x v'
  simp only [v', ContinuousLinearEquiv.apply_symm_apply] at hleft hright
  rw [hleft,
    edge_unit_smul (I := I) (M := M) g c
      (rawTensorConnLapSmooth (I := I) g 0 2 W) x v,
    hright,
    iteratedCovGrad_smul, operatorFieldApplication_smul_right,
    edge_unit_smul (I := I) (M := M) g c
      (operatorFieldApply (I := I) (M := M) g 4 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 W)) x v]

omit [SigmaCompactSpace M] in
private theorem edge_core_smul
    (g gm : SmoothRiemannianMetric I M)
    (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
    (c : Real) (W : SmoothCcTensor g 0 2) :
    ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 (c • W) =
      c • ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 W := by
  simp only [ricciDeTurckLowOrderAction, firstOrderCoefficientAction, deTurckPrincipalCometricArm,
    edge_lap_smul, iteratedCovGrad_smul, operatorFieldApplication_smul_right]
  module

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma edge_bound_mono
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {a b : Real} (hab : a ≤ b)
    (ha : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) a) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) b := by
  intro x v w
  exact (ha x v w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

theorem ricciDeTurckLowOrderAction_pairing_upper_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2)
        (_hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g W x v w =
            smoothCcTensorBilinForm (I := I) g W x w v)
        {B0 B1 delta s : Real},
        0 ≤ B0 → 0 ≤ B1 → delta < 1 / 2 → 0 ≤ delta →
        (hWbound : metricCauchySchwarzBound (I := I) (M := M) g
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
            (ricciDeTurckLowOrderAction (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W
                hWbound s) C0 C1 W).toFun ≤
          -(1 / 4 : Real) *
              ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
            (B0 + B1 ^ 2) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hcore⟩ := ricciDeTurckLowOrderAction_pairing_bound (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro C0 C1 W hWsymm B0 B1 delta s hB0 hB1 hdelta hdelta0
    hWbound hsmall hC0 hC1 hs
  let P : SmoothCcTensor g 0 2 := s • W
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPathFromZero (I := I) (M := M) g W hWbound s
  have hdelta_lt : delta < 1 := lt_trans hdelta (by norm_num)
  have hscc : s ∈ Set.Icc (0 : Real) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hsSmall : s ∈ metricPerturbationPathDomain (δ := delta) (δ' := 0) :=
    Icc_subset_metricPerturbationPathDomain hdelta_lt (by norm_num) hscc
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    have hpath := metricPerturbationPath_inner_of_mem (I := I) (M := M)
      g W 0 hWbound (zero_metricPerturbation_bound (I := I) (M := M) g)
      hsSmall y v w
    simpa only [gm, metricPerturbationPathFromZero, P, convexPerturbation, smul_zero,
      zero_add] using hpath
  have hPraw := gFibreOpBound_ccTensorBilinSymm_smul
    (I := I) (M := M) g s W hWbound
  have hsabs : |s| ≤ 1 := by
    rw [abs_of_pos hs.1]
    exact hs.2.le
  have hrad : |s| * delta ≤ delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsabs hdelta0
  have hPbound : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta :=
    edge_bound_mono (I := I) (M := M) g P hrad
      (by simpa only [P] using hPraw)
  have hWfix : ccTensor02Symm (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g W hWsymm
  have hPfix : ccTensor02Symm (I := I) (M := M) g P = P := by
    simp only [P, symmS_smul, hWfix]
  have hp := hcore gm C0 C1 P hB0 hB1 hdelta hdelta0
    htie hPbound hPfix hsmall hC0 hC1
  have hcoreSmul :
      ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 P =
        s • ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 W := by
    simpa only [P] using
      edge_core_smul (I := I) (M := M) g gm C0 C1 s W
  have hpair :
      tensorL2Inner (I := I) (M := M) g 0 2 P.toFun
          (ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 P).toFun =
        s ^ 2 * tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) P
      (ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 P),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 W),
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
      (ricciDeTurckLowOrderAction (I := I) (M := M) g gm C0 C1 W).toFun ≤ _
  nlinarith only [hp, hs2]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem edge_l2_of_riemannianFiberNormSq
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

theorem ricciDeTurckTopOrderPairing_upper_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ delta0 K : Real, 0 < delta0 ∧ delta0 < 1 / 2 ∧ 0 ≤ K ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (_hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g W x v w =
            smoothCcTensorBilinForm (I := I) g W x w v)
        {delta : Real}, 0 ≤ delta → delta ≤ delta0 →
        (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) delta) →
        ∀ (qA qB : Fin 4 → Equiv.Perm (Fin 4))
          (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real),
          (∀ i, |epsilon i| ≤ 1) →
          ∀ s ∈ Set.Icc (0 : Real) 1,
            (⟪W, (operatorFieldApply (I := I) (M := M) g 2 2
              (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
                qA qB q epsilon s) W)⟫_ℝ : Real) ≤
              (1 / 4 : Real) *
                  ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
                K * ‖W‖ ^ 2 := by
  classical
  obtain ⟨C0, hC0, hzero⟩ := ricciDeTurckTopOrderPairingAdjoint_norm_bound (I := I) (M := M) g
  obtain ⟨C1, hC1, hone⟩ := ricciDeTurckTopOrderPairingAdjoint_covariantDerivative_bound (I := I) (M := M) g
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
    ricciDeTurckTopOrderPairingAdjoint (I := I) (M := M) g W hdelta hdeltaZ
      qA qB q epsilon s
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  have hP : ‖P‖ ≤ Real.sqrt C0 * delta * ‖W‖ := by
    apply edge_l2_of_riemannianFiberNormSq (I := I) (M := M) g 0 4 0 2 P W
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
    apply edge_l2_of_riemannianFiberNormSq (I := I) (M := M) g 0 5 0 3
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
      (⟪W, (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W)⟫_ℝ : Real) ≤
        (A * delta * ‖W‖ + B * delta * ‖D‖) * ‖D‖ := by
    calc
      (⟪W, (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W)⟫_ℝ : Real) =
          -⟪covDivergence (I := I) (M := M) g 3 P, D⟫_ℝ := by
        simpa only [P, D] using
          ricciDeTurckTopOrderPairing_green (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s
      _ ≤ |⟪covDivergence (I := I) (M := M) g 3 P, D⟫_ℝ| := by
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
    have hcoef : 0 ≤ 2 * A ^ 2 := by positivity
    have hdeltaCoef : 2 * A ^ 2 * delta ^ 2 ≤ 2 * A ^ 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hdelta_sq hcoef
    exact mul_le_mul_of_nonneg_right
      hdeltaCoef (sq_nonneg ‖W‖)
  dsimp only [D] at hpair hcross hgrad ⊢
  calc
    (⟪W, (operatorFieldApply (I := I) (M := M) g 2 2
      (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
        qA qB q epsilon s) W)⟫_ℝ : Real) ≤
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

theorem ricciDeTurckRhsSlope_pairing_upper_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C delta0 K : Real,
      0 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 / 2 ∧ 0 ≤ K ∧
      ∀ (C0 : SmoothCcTensor g 2 2) (C1 : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2)
        (_hWsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g W x v w =
            smoothCcTensorBilinForm (I := I) g W x w v)
        {B0 B1 delta s : Real},
        0 ≤ B0 → 0 ≤ B1 → 0 ≤ delta → delta ≤ delta0 →
        (hdelta : metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) delta) →
        (hdeltaZ : metricCauchySchwarzBound (I := I) (M := M) g
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
            (ricciDeTurckLowOrderAction (I := I) (M := M) g
                (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) C0 C1 W +
              operatorFieldApply (I := I) (M := M) g 2 2
                (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
                  qA qB q epsilon s) W).toFun ≤
          (B0 + B1 ^ 2 + K) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hcore⟩ := ricciDeTurckLowOrderAction_pairing_upper_bound (I := I) (M := M) g
  obtain ⟨delta0, K, hdelta0, hdelta0_half, hK, htop⟩ :=
    ricciDeTurckTopOrderPairing_upper_bound (I := I) (M := M) g
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
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
              qA qB q epsilon s) W).toFun ≤
        (1 / 4 : Real) *
            ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
          K * ‖W‖ ^ 2 := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
          qA qB q epsilon s) W)]
    exact htop0
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (ricciDeTurckLowOrderAction (I := I) (M := M) g
              (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) C0 C1 W +
            operatorFieldApply (I := I) (M := M) g 2 2
              (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
                qA qB q epsilon s) W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (ricciDeTurckLowOrderAction (I := I) (M := M) g
            (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) C0 C1 W).toFun +
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
              qA qB q epsilon s) W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (ricciDeTurckLowOrderAction (I := I) (M := M) g
          (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) C0 C1 W +
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (ricciDeTurckLowOrderAction (I := I) (M := M) g
          (metricPerturbationPathFromZero (I := I) (M := M) g W hdelta s) C0 C1 W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g W hdelta hdeltaZ
            qA qB q epsilon s) W),
      inner_add_right]
  rw [hadd]
  nlinarith

end Spectral
end Analysis
end DifferentialGeometry

end
