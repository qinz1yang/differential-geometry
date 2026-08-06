import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzPathIntegralDeviation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmOneAllOrderJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzBackgroundOneDimensional
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciArmPrincipalCoeffBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartLieDeriv
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm2CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzRicciArmCoeffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLiePathValueDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieArmChartValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionL2JetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmDiffL2TameBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzPhiMetTotalCurvatureFold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzDegenerateOneDimensionalVanishing
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum jointContMDiff_toModel_continuous_slice
  hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.DeTurck (cometricLmodel)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField
  deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth
  deTurckLieCoeffField_realizedFam_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA
  deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)

set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_connDiff_realizedFam_allOrder_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Analysis.Sobolev.deTurckLieTraceCoeffPiece (I := I) (M := M)
                g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Geometry.Curvature.connDiffSection (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform
      (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd0, hΛcd_nn, hFcd0_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (C2 i * ((fr ^ 2 * Λcd) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fcd l)))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fcd l :=
      Finset.sum_nonneg fun l _ => hFcd_nn l
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              g₀))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * Λcd)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))‖ ^ 2 ≤
          fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                  g₀)))‖ ^ 2 ≤
            fr ^ 2 * (Fcd l * (2 * W)) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (hFcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
          have hl2 : l + 2 ≤ i + 2 := by
            have := Finset.mem_range.mp hl; omega
          have hwin := hPwin (l + 2) hl2
          have := hFcd_nn l
          nlinarith
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        have : (∑ l ∈ Finset.range (i + 1), Fcd l) * (2 * W) =
            (2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W := by ring
        rw [this]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λcd))
        ((2 * Qth i) * W) (fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λcd))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ'
            ρ
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          (C2 i * ((fr ^ 2 * Λcd) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fcd l)))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fcd l :=
          Finset.sum_nonneg fun l _ => hFcd_nn l
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        positivity
      dsimp only
      nlinarith

set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_connDiffBg_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Analysis.Sobolev.deTurckLieTraceCoeffPiece (I := I) (M := M)
                g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Analysis.Sobolev.lieArm1ConnDiffBgCc (I := I) (M := M)
                  g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform
      (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd0, hΛcd_nn, hFcd0_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (C2 i * ((fr ^ 2 * (2 * Λcd + 2 * Λfx)) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), (4 * Fcd l
        + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) :=
      Finset.sum_nonneg fun l _ => by
        have := hFcd_nn l
        positivity
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    have h5 : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hΨ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
          2 * Λcd + 2 * Λfx := by
        intro x
        rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
        refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
        have h1 := hcd0 x
        have h2 := hΛfx x
        linarith
      have hΨ0_nn : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx))) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hΨ0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          fr ^ 2 * ((∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
            fr ^ 2 * ((4 * Fcd l
              + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) * W) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hdecomp : ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
              2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (connDiffSection (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2
                + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
            rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
            exact lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 1 2 l _ _
          have hcdl : ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
              Fcd l * (2 * W) := by
            refine le_trans (hFcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
            have hl2 : l + 2 ≤ i + 2 := by
              have := Finset.mem_range.mp hl; omega
            have hwin := hPwin (l + 2) hl2
            have := hFcd_nn l
            nlinarith
          have hBfx_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := sq_nonneg _
          nlinarith [hdecomp, hcdl, hBfx_nn, hW1]
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx)))
        ((2 * Qth i) * W)
        (fr ^ 2 * ((∑ l ∈ Finset.range (i + 1), (4 * Fcd l
          + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ'
            ρ
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          (C2 i * ((fr ^ 2 * (2 * Λcd + 2 * Λfx)) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (∑ l ∈ Finset.range (i + 1), (4 * Fcd l
                + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                    (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) :=
          Finset.sum_nonneg fun l _ => by
            have := hFcd_nn l
            positivity
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        have h5 : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
        positivity
      dsimp only
      nlinarith

set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_psiB_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Analysis.Sobolev.deTurckLieTraceCoeffPiece (I := I) (M := M)
                g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Analysis.Sobolev.lieArm1PsiB (I := I) (M := M)
                  g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform
      (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fpb, hFpb_nn, hFpbJ⟩ :=
    pAO_lieArm1PsiB_jetL2_tame (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λpb, Fpb0, hΛpb_nn, hFpb0_nn, hpb⟩ :=
    lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (C2 i * ((fr ^ 2 * Λpb) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fpb l)))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fpb l :=
      Finset.sum_nonneg fun l _ => hFpb_nn l
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hpb0, _⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * Λpb)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1PsiB (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
            fr ^ 2 * (Fpb l * (2 * W)) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (hFpbJ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
          have hl2 : l + 2 ≤ i + 2 := by
            have := Finset.mem_range.mp hl; omega
          have hwin := hPwin (l + 2) hl2
          have := hFpb_nn l
          nlinarith
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        have : (∑ l ∈ Finset.range (i + 1), Fpb l) * (2 * W) =
            (2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W := by ring
        rw [this]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1PsiB (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λpb))
        ((2 * Qth i) * W) (fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λpb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ'
            ρ
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          (C2 i * ((fr ^ 2 * Λpb) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fpb l)))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fpb l :=
          Finset.sum_nonneg fun l _ => hFpb_nn l
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        positivity
      dsimp only
      nlinarith

private theorem norm_sq_le_of_norm_le_mul_sqrt {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {B Sw W : ℝ} (hSw_sq : Sw ^ 2 = W) (_hB_nn : 0 ≤ B * Sw)
    (h : ‖v‖ ≤ B * Sw) : ‖v‖ ^ 2 ≤ B ^ 2 * W := by
  have h2 := pow_le_pow_left₀ (norm_nonneg v) h 2
  rwa [mul_pow, hSw_sq] at h2

set_option backward.isDefEq.respectTransparency false in
theorem deTurckLieArm1Coeff_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieArm1Piece_connDiff_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieArm1Piece_psiB_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := by
    rw [hW_def]
    positivity
  set Sw : ℝ := Real.sqrt W with hSw_def
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSw_sq : Sw ^ 2 = W := Real.sq_sqrt hW_nn
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ (connDiffSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPc_nn i)] at h
    exact h
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPbg_nn i)] at h
    exact h
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPb_nn i)] at h
    exact h
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine norm_sq_le_of_norm_le_mul_sqrt hSw_sq (by positivity) ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := lieArm1_norm_block6_le'_fw
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have hblock2 := lieArm1_norm_block6_le'_fw
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have h1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieArm1SigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have h6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have h11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have h12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieArm1SigmaC lieArm1RhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciArm1CorrField_allOrder_tameEnvelope_interface
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    Analysis.Parabolic.TensorSpectral.exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  have hid :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.2.2.2.2
  rw [show linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder1Coeff
          (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s from hid s]
  exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i s hs

end DifferentialGeometry.Analysis.Spectral

end
