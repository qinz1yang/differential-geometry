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
open DifferentialGeometry.Geometry.Connection


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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

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

private lemma convexCombination_le_fw {a b c t : ℝ} (ha : a ≤ c) (hb : b ≤ c)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a + t * b ≤ c := by
  nlinarith

private lemma convexCombination_nonneg_fw {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t) * a + t * b := by
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht0 hb)

omit [BoundarylessManifold I M] in
private theorem realizedFam_gInvDiffSlotCoeff_rfns_le_fw
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    {βT βT' : ℝ} (hβT_nn : 0 ≤ βT) (hβT'_nn : 0 ≤ βT')
    (hβT : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) βT)
    (hβT' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') βT')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (max βT βT' / (1 - δ₀))) ^ 2 := by
  set g₁ := realizedFam (I := I) g₀ T T' hδ hδ' t with hg₁_def
  set δc : ℝ := min ((1 - t) * βT' + t * βT) δ₀ with hδc_def
  have hβconv : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
      ((1 - t) * βT' + t * βT) :=
    convexPerturbation_gFibreOpBound (I := I) g₀ T T' hβT hβT' ht.1 ht.2
  have hδconv : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
      ((1 - t) * δ' + t * δ) :=
    convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' ht.1 ht.2
  have hδ₀b : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δ₀ :=
    gFibreOpBound_mono_fw (I := I) (M := M) g₀ _
      (convexCombination_le_fw hδ'_le hδ_le ht.1 ht.2) hδconv
  have hmin : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δc :=
    gFibreOpBound_min_fw (I := I) (M := M) g₀ _ hβconv hδ₀b
  have hδc_nn : 0 ≤ δc :=
    le_min (convexCombination_nonneg_fw hβT'_nn hβT_nn ht.1 ht.2) hδ₀_nn
  have hδc_lt : δc < 1 := lt_of_le_of_lt (min_le_right _ _) hδ₀
  have htmem : t ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet (lt_of_le_of_lt hδ_le hδ₀)
      (lt_of_le_of_lt hδ'_le hδ₀) ht
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t) y v w := by
    intro y v w
    rw [hg₁_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' htmem y v w
  have hendo :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.riemannianFiberNormSq_gInvDiffSlotEndo_le
      (I := I) (M := M) g₀ g₁ _ htie hδc_lt hδc_nn hmin x
  have hslot : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (δc / (1 - δc))) ^ 2 := by
    rw [show (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x =
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonDiffSlotEndo
            (I := I) g₀ g₁ x)) from rfl]
    exact hendo
  have hmaxβ_nn : 0 ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
  have hδc_le : δc ≤ max βT βT' :=
    (min_le_left _ _).trans
      (convexCombination_le_fw (le_max_right _ _) (le_max_left _ _) ht.1 ht.2)
  have hdenom : 1 - δ₀ ≤ 1 - δc := sub_le_sub_left (min_le_right _ _) 1
  have hratio : δc / (1 - δc) ≤ max βT βT' / (1 - δ₀) :=
    div_le_div₀ hmaxβ_nn hδc_le (sub_pos.mpr hδ₀) hdenom
  refine hslot.trans (pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hδc_nn (sub_nonneg.mpr hδc_lt.le)))
    (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)) 2)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem deTurckPhiMetTotal_deviation_rfns_le_gInvDiffSlotCoeff_fw
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (CTH CR : ℝ) (x : M)
    (hTH : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CTH * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x))
    (hR : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CR * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁
          - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
      (8 * CTH + 8 * CR) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) := by
  set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
  set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
  set DTHs : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ g₁
      - traceHessianCoeff (I := I) (M := M) g₀ g₀
  set DRs : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
  have hdev : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁
        - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT
        - (DRs + DRs) := by
    rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₁,
      deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρA,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρAT]
    dsimp [ρA, ρAT, DTHs, DRs]
    abel
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁
          - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x)
        + 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
        + 8 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) := by
    rw [hdev]
    have h1 := rfns_toSection_sub_le_fw (I := I) (M := M) g₀ 4 2
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT) (DRs + DRs) x
    have h2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 4 2
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)
      (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT) x
    have h3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 4 2 DRs DRs x
    linarith
  have hAr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
    rw [reindexCoeffGen_toSection]
    exact
      Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
      (I := I) (M := M) g₀ 4 2 x ρA
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        DTHs.toSection x)
  have hATr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
    rw [reindexCoeffGen_toSection]
    exact
      Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
      (I := I) (M := M) g₀ 4 2 x ρAT
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        DTHs.toSection x)
  rw [hAr, hATr] at h0
  change riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) ≤ _ at hTH
  change riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) ≤ _ at hR
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ c Γd : ℝ, 0 ≤ c ∧ 0 ≤ Γd ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        {βT βT' : ℝ} (_hβT_nn : 0 ≤ βT) (_hβT'_nn : 0 ≤ βT')
        (_hβT : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT)
        (_hβT' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
          βT'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
              - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
          (c * max βT βT') ^ 2) ∧
        (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
              - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2) ≤ Γd ^ 2 := by
  classical
  obtain ⟨CTH, hCTH_nn, hCTH⟩ :=
    traceHessianCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff (I := I)
      (M := M) g₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff
      (I := I) (M := M) g₀
  obtain ⟨DTH, hDTH_nn, hDTH⟩ :=
    traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform (I := I) (M := M) g₀
      a ha_super hR hδ₀
  obtain ⟨DR, hDR_nn, hDR⟩ :=
    ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  set Sco : ℝ := 8 * CTH 0 + 8 * CR 0 with hSco_def
  have hSco_nn : 0 ≤ Sco := by
    have := hCTH_nn 0
    have := hCR_nn 0
    rw [hSco_def]
    linarith
  set Γsq : ℝ := 8 * (∑ i ∈ Finset.range (a + 1), DTH i)
    + 8 * (∑ i ∈ Finset.range (a + 1), DR i) with hΓsq_def
  have hΓsq_nn : 0 ≤ Γsq := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (a + 1), DTH i :=
      Finset.sum_nonneg fun i _ => hDTH_nn i
    have h2 : 0 ≤ ∑ i ∈ Finset.range (a + 1), DR i :=
      Finset.sum_nonneg fun i _ => hDR_nn i
    rw [hΓsq_def]
    linarith
  refine ⟨Real.sqrt Sco * (dim / (1 - δ₀)), Real.sqrt Γsq,
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hdim_nn (le_of_lt h1δ₀)),
    Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' βT βT' hβT_nn hβT'_nn hβT hβT' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA with hρA_def
  set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
    with hρAT_def
  set Ψdev : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s)
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ with hΨdev_def
  have hdev_eq : ∀ s : ℝ, Ψdev s =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT
        - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
          + (ricciArmPrincipalCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)) := by
    intro s
    simp only [hΨdev_def]
    rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s),
      deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρA,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρAT]
    abel
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') :=
    deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hjdev : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψdev
      (δ := δ) (δ' := δ') := by
    have hconst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection.contMDiff.comp_contMDiffOn
        contMDiffOn_fst
    have hj2' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have h := hj2
      rw [linearizedRicciThreeArmHjoint] at h
      exact h
    have hsub := jointTotalSpaceRS_sub_fw (I := I) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
      (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1)
      hj2' hconst
    refine hsub.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    simp only [hΨdev_def]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  set Pdev : SmoothCcTensor g₀ 4 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψdev
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev with hPdev_def
  have hc2tot : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro x
    have h := hj2
    rw [linearizedRicciThreeArmHjoint] at h
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s))
      (realizedSmallSet (δ := δ) (δ' := δ')) h x
  have hcdev : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψdev t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψdev
      (realizedSmallSet (δ := δ) (δ' := δ')) hjdev x
  have heq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ = Pdev := by
    have hPeq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
          (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply Tensor0SBundle.TensorRSSpace.toModel_injective
    change Tensor0SBundle.TensorRSSpace.toModel
        ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) =
      Tensor0SBundle.TensorRSSpace.toModel (Pdev.toSection x)
    rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x
        - (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [Tensor0SBundle.TensorRSSpace.toModel_sub, hPeq, hPdev_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel]
    have hint : IntervalIntegrable (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hc2tot x).mono hSI).intervalIntegrable
    rw [show (∫ t in (0:ℝ)..1, Tensor0SBundle.TensorRSSpace.toModel ((Ψdev t).toSection x)) =
        ∫ t in (0:ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel
            ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x)
          - Tensor0SBundle.TensorRSSpace.toModel
            ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x)) from
      intervalIntegral.integral_congr (fun t _ => by
        simp only [hΨdev_def]
        rw [show ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t))
            - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x
            - (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [Tensor0SBundle.TensorRSSpace.toModel_sub])]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  refine ⟨?_, ?_⟩
  · intro x
    rw [heq, hPdev_def]
    have hmaxβ_nn : (0 : ℝ) ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
    have hcb_nn : (0 : ℝ) ≤ Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (div_nonneg hdim_nn (le_of_lt h1δ₀))) hmaxβ_nn
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Ψdev t).toSection x)) ≤
          Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' := by
      intro t ht
      set g₁ := realizedFam (I := I) g₀ T T' hδ hδ' t with hg₁_def
      have hTH0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((traceHessianCoeff (I := I) (M := M) g₀ g₁
            - traceHessianCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
          CTH 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) := by
        have h := hCTH g₁ 0 x
        simpa using h
      have hR0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
          CR 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) := by
        have h := hCR g₁ 0 x
        simpa using h
      have hdev := deTurckPhiMetTotal_deviation_rfns_le_gInvDiffSlotCoeff_fw
        (I := I) (M := M) g₀ g_bg g₁ (CTH 0) (CR 0) x hTH0 hR0
      have hslot := realizedFam_gInvDiffSlotCoeff_rfns_le_fw
        (I := I) (M := M) g₀ hδ₀ hδ₀_nn T T' hδ_le hδ hδ'_le hδ'
          hβT_nn hβT'_nn hβT hβT' t ht x
      have hdev' : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Ψdev t).toSection x) ≤
          Sco * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) := by
        simpa only [hΨdev_def, hSco_def] using hdev
      have hmul := mul_le_mul_of_nonneg_left hslot hSco_nn
      have hc2 : (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 =
          Sco * ((Module.finrank ℝ E : ℝ) * (max βT βT' / (1 - δ₀))) ^ 2 := by
        rw [show (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 =
            Real.sqrt Sco ^ 2 *
              ((Module.finrank ℝ E : ℝ) * (max βT βT' / (1 - δ₀))) ^ 2 from by
              rw [hdim_def]
              ring,
          Real.sq_sqrt hSco_nn]
      have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Ψdev t).toSection x) ≤
          (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 :=
        hdev'.trans (hmul.trans_eq hc2.symm)
      calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((Ψdev t).toSection x))
          ≤ Real.sqrt ((Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2) :=
            Real.sqrt_le_sqrt hbound
        _ = Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' := Real.sqrt_sq hcb_nn
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Ψdev
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev x
      (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') hcb_nn
      ((hcdev x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
  · rw [heq, hPdev_def]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2) ≤
          Real.sqrt Γsq ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hΓsq_nn]
      set g₁ := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
      set DTHs : SmoothCcTensor g₀ 4 2 :=
        traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀ with hDTHs_def
      set DRs : SmoothCcTensor g₀ 4 2 :=
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hDRs_def
      have hs1 : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2) ≤
          2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
              + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2)
          + 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (DRs + DRs)‖ ^ 2) := by
        have h := Finset.sum_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (Ψdev s)‖ ^ 2)
          (g := fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2
            + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2)
          (s := Finset.range (a + 1)) (fun i _ => by
            rw [hdev_eq s]
            exact normSq_icg_sub_le_fw (I := I) (M := M) g₀ 4 2 i _ _)
        calc (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2)
            ≤ ∑ i ∈ Finset.range (a + 1),
              (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                    + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2
                + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) := h
          _ = 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                  + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2)
              + 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DRs + DRs)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hAB := jetTowerSum_add_le (I := I) g₀ 4 2 (a + 1)
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)
      have hCC := jetTowerSum_add_le (I := I) g₀ 4 2 (a + 1) DRs DRs
      have hAeq : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)‖ ^ 2) =
          ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => normSq_icg_reindex_eq_fw (I := I) (M := M) g₀ DTHs ρA i)
      have hATeq : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) =
          ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => normSq_icg_reindex_eq_fw (I := I) (M := M) g₀ DTHs ρAT i)
      have hDTHsum : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), DTH i :=
        Finset.sum_le_sum (fun i hi => by
          rw [hDTHs_def, hg₁_def]
          exact hDTH T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs)
      have hDRsum : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), DR i :=
        Finset.sum_le_sum (fun i hi => by
          rw [hDRs_def, hg₁_def]
          exact hDR T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs)
      rw [hAeq, hATeq] at hAB
      rw [hΓsq_def]
      linarith
    exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 4 a Ψdev hSI hSopen hjdev
      (Real.sqrt_nonneg _) hjet

set_option backward.isDefEq.respectTransparency false in
theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w
            v)
        {βT βT' : ℝ} (_hβT_nn : 0 ≤ βT) (_hβT'_nn : 0 ≤ βT')
        (_hβT : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT)
        (_hβT' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
          βT'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤
            (ΛC * max βT βT') ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨K₀, hK₀fold⟩ :=
    exists_deTurckPhiMetTotal_background_curvatureFold_of_symm (I := I) (M := M) g₀ g_bg
  obtain ⟨ΛA, ΓA, hΛA_nn, hΓA_nn, harm⟩ :=
    deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm
      (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨cD, ΓD, hcD_nn, hΓD_nn, hdev⟩ :=
    deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
  obtain ⟨ΛK, hΛK_nn, hΛK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 K₀
  set ΓK : ℝ := Real.sqrt (∑ i ∈ Finset.range (a + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) with hΓK_def
  have hΓK_nn : 0 ≤ ΓK := Real.sqrt_nonneg _
  have hΓKjet : (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) ≤ ΓK ^ 2 := by
    rw [hΓK_def, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hsq_mono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → s ^ 2 ≤ t ^ 2 := by
    intro s t hs hst
    nlinarith
  refine ⟨max (Real.sqrt (2 * ΛA ^ 2 + 2 * Real.sqrt ΛK ^ 2)) (max ΛA cD),
    max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm βT βT' hβT_nn hβT'_nn hβT hβT'
    hTball hT'ball
  obtain ⟨C₀, C₁, hidArm, hC₀sup, hC₁sup, hC₀jet, hC₁jet⟩ :=
    harm T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨hdevsup, hdevjet⟩ :=
    hdev T T' hδ_le hδ hδ'_le hδ' hβT_nn hβT'_nn hβT hβT' hTball hT'ball
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w = smoothCcTensorBilinForm (I := I) g₀
        (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub_fw, ccTensorBilin_sub_fw, hTsymm x v w, hT'symm x v w]
  have hKfold := hK₀fold (T - T') hSsymm
  have hKfold' : operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) -
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 K₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) := by
    rw [← appCc_sub_left]
    exact hKfold
  have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact
      Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
        (I := I) (M := M) g₀ (T - T') x v
  refine ⟨C₀ + K₀, C₁,
    deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ', hidArm, hlift,
      appCc_add_left, appCc_sub_left, ← hKfold']
    abel
  · intro x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (K₀.toSection x) ≤
        Real.sqrt ΛK ^ 2 := by
      rw [Real.sq_sqrt hΛK_nn]
      exact hΛK x
    exact (threeArmCoeffSum_rfns_le (I := I) g₀ C₀ K₀ ΛA (Real.sqrt ΛK) x (hC₀sup x) h1).trans
      (hsq_mono _ _ (Real.sqrt_nonneg _) (le_max_left _ _))
  · intro x
    exact (hC₁sup x).trans
      (hsq_mono _ _ hΛA_nn (le_trans (le_max_left ΛA cD) (le_max_right _ _)))
  · intro x
    have hm_nn : 0 ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
    refine (hdevsup x).trans (hsq_mono _ _ (mul_nonneg hcD_nn hm_nn) ?_)
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_right ΛA cD) (le_max_right _ _)) hm_nn
  · calc (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (C₀ + K₀)‖ ^ 2)
        ≤ 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) +
            2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) :=
          jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1) C₀ K₀
      _ ≤ 2 * ΓA ^ 2 + 2 * ΓK ^ 2 := by linarith [hC₀jet, hΓKjet]
      _ ≤ (max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD)) ^ 2 := by
          have hs : Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2) ^ 2 = 2 * ΓA ^ 2 + 2 * ΓK ^ 2 :=
            Real.sq_sqrt (by positivity)
          have hle : Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2) ≤
              max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD) := le_max_left _ _
          nlinarith [hs, hle, Real.sqrt_nonneg (2 * ΓA ^ 2 + 2 * ΓK ^ 2)]
  · exact hC₁jet.trans
      (hsq_mono _ _ hΓA_nn (le_trans (le_max_left ΓA ΓD) (le_max_right _ _)))
  · exact hdevjet.trans
      (hsq_mono _ _ hΓD_nn (le_trans (le_max_right ΓA ΓD) (le_max_right _ _)))

set_option backward.isDefEq.respectTransparency false in
lemma smoothCcToTensorHs_zero_norm_le_fw (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
  have hzero : smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    refine DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    rw [show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _]
    rw [DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
      inner_zero_right]
    rfl
  rw [hzero, norm_zero]
  exact hR₀

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
lemma ccTensorBilin_zero_symm_fw (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w =
      smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x w v := by
  have h0 : ∀ (u₁ u₂ : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x u₁ u₂ = 0 := by
    intro u₁ u₂
    have hs := ccTensorBilin_sub_fw (I := I) (M := M) g₀
      (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2) x u₁ u₂
    rw [sub_zero] at hs
    linarith
  rw [h0, h0]

set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiZero_jointSmooth_fw (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
        + (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)) (δ := δ) (δ' := δ') :=
  threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _
    (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
    (deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth (I := I) g₀ T T' hδ
      hδ' g_bg)

set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiOne_jointSmooth_fw (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
        + deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 3 _ _
    (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
    (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)

set_option backward.isDefEq.respectTransparency false in
noncomputable def deTurckPhiZeroPathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 2 2
    (fun s => (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiZero_jointSmooth_fw (I := I) (M := M) g₀ g_bg T T' hδ hδ')

set_option backward.isDefEq.respectTransparency false in
noncomputable def deTurckPhiOnePathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 3 2
    (fun s => (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiOne_jointSmooth_fw (I := I) (M := M) g₀ g_bg T T' hδ hδ')

set_option backward.isDefEq.respectTransparency false in
theorem deTurckRHSArmDiff_eq_pathIntegralCoeff_triple_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v) :
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' =
      operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
  classical
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w = smoothCcTensorBilinForm (I := I) g₀
        (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x v w,
      ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x w v, hTsymm x v w, hT'symm x v w]
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) with hΨ₀def
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hΨ₁def
  set Ψ₂ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s) with hΨ₂def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀ (δ := δ) (δ' := δ') := by
    rw [hΨ₀def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth (I := I) g₀ T T' hδ
        hδ' g_bg)
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁ (δ := δ) (δ' := δ') := by
    rw [hΨ₁def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 3 _ _
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψ₂ (δ := δ) (δ' := δ') := by
    rw [hΨ₂def]
    exact deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₂ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hj2 x
  have hPi0 : deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 := rfl
  have hPi1 : deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 := rfl
  have hPitop : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  rw [hPi0, hPi1, hPitop]
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
  set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
  rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
  rw [show (unitModel (I := I) (M := M) g₀ 2
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
      deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
    unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
      (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
  rw [show (unitModel (I := I) (M := M) g₀ 2
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
      deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
    unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
      (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') rfl x v]
  have hsplit : ∀ (g : SmoothRiemannianMetric I M),
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) =
        ((-2 : ℝ) • ricciTensor (I := I) g x (v 0) (v 1)) +
          lieDerivMetricClm (I := I) g
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
    intro g
    rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rfl
  rw [hsplit g₁, hsplit g₁']
  rw [show ((-2 : ℝ) • ricciTensor (I := I) g₁ x (v 0) (v 1) +
          lieDerivMetricClm (I := I) g₁
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) -
        ((-2 : ℝ) • ricciTensor (I := I) g₁' x (v 0) (v 1) +
          lieDerivMetricClm (I := I) g₁'
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) =
      ((-2 : ℝ) • (ricciTensor (I := I) g₁ x (v 0) (v 1) -
          ricciTensor (I := I) g₁' x (v 0) (v 1))) +
        (lieDerivMetricClm (I := I) g₁
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
          lieDerivMetricClm (I := I) g₁'
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) from by
    simp only [smul_sub]; ring]
  rw [hg₁, hg₁']
  rw [ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
  rw [lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add
    ((DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_intervalIntegrable
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)).const_mul (-2 : ℝ))
    (linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1))]
  have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s
        + linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
        + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
        + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
    rw [MeasureTheory.ae_iff]
    have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
    refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hsmem, hsneq⟩ := hs
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
    refine hsneq ?_
    have hRid : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
            + operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
            + operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      obtain ⟨_, _, _, hident, _, _⟩ :=
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
          (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
      exact hident hTsymm hT'symm s hsIoo x v hδ_lt hδ'_lt
    have hLid := linearizedDeTurckLieAt_eq_threeArm_plain_of_symm_fw (I := I) (M := M)
      g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hSsymm hsIoo x v
    have hRid' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      rw [hRid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
    have hLid' : linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      rw [hLid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
    have e0 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v =
        (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v := by
      simp only [hΨ₀def]
      rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
    have e1 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v =
        (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v := by
      simp only [hΨ₁def]
      rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
    have e2 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v =
        (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      simp only [hΨ₂def]
      rw [deTurckPhiMetTotal_realizedFam_eq_neg_two_smul_fw (I := I) (M := M)
        g₀ g_bg T T' hδ hδ' s]
      rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
    rw [hRid', hLid', e0, e1, e2]
    ring
  rw [intervalIntegral.integral_congr_ae hintegrand]
  have hI0 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v) MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) hSI hc0 x v
  have hI1 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v) MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 3 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) hSI hc1 x v
  have hI2 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) hSI hc2 x v
  rw [intervalIntegral.integral_add (hI0.add hI1) hI2, intervalIntegral.integral_add hI0 hI1]
  have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Ψ₀
    (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
  have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Ψ₁
    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
  have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Ψ₂
    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
  rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame, he0, he1, he2]


end DifferentialGeometry.Analysis.Spectral

end

