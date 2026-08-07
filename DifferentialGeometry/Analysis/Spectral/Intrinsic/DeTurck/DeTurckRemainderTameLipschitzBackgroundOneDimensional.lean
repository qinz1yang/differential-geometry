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
open Analysis.Parabolic.TensorSpectral

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_tl_icg_zero (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_add (I := I) g r s j 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := iteratedCovGrad (I := I) g r s j 0)
    (by rw [← h, add_zero])).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_toSection_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ((0 : SmoothCcTensor g r s).toSection x) = 0 := by
  have h : ((0 : SmoothCcTensor g r s) + 0).toSection x =
      (0 : SmoothCcTensor g r s).toSection x + (0 : SmoothCcTensor g r s).toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [add_zero] at h
  exact (add_left_cancel (a := (0 : SmoothCcTensor g r s).toSection x)
    (by rw [← h, add_zero])).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private lemma rfns_tl_add_le_sq_sqrt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) ≤
      (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b)) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  set A := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) a) with hA
  set B := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) b) with hB
  set C := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) with hC
  have hsymm : tensorInnerPointwise (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) a) = C := by
    rw [hC, tensorInnerPointwise_symm]
  rw [hsymm]
  have hA0 : 0 ≤ A := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have hB0 : 0 ≤ B := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have hC2 : C ^ 2 ≤ A * B := tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s x _ _
  have hCle : C ≤ Real.sqrt A * Real.sqrt B := by
    calc C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hC2
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  nlinarith [hCle, hsA, hsB]

set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_young_sq (u v θ : ℝ) (hθ : 0 < θ) :
    (u + v) ^ 2 ≤ (1 + θ) * u ^ 2 + (1 + θ⁻¹) * v ^ 2 := by
  have hθ' : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hkey : 2 * (u * v) ≤ θ * u ^ 2 + θ⁻¹ * v ^ 2 := by
    have h0 : 0 ≤ (θ * u - v) ^ 2 := sq_nonneg _
    have hexp : θ * (θ * u ^ 2 + θ⁻¹ * v ^ 2 - 2 * (u * v)) = (θ * u - v) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_pos hθ hθ]
  nlinarith [hkey]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_fibreConst_one (h1 : Module.finrank ℝ E = 1) :
    deTurckArmFibreConst (Module.finrank ℝ E) = 1 := by
  rw [h1]
  rw [deTurckArmFibreConst]
  rw [Nat.cast_one, one_pow, Real.sqrt_one]

set_option backward.isDefEq.respectTransparency false in
private lemma rfns_tl_sqrt_mul_self_eq_fibreConst (n : ℕ) :
    Real.sqrt n * n = deTurckArmFibreConst n := by
  rw [deTurckArmFibreConst]
  rw [show ((n : ℝ)) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 from by ring]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [Real.sqrt_sq (Nat.cast_nonneg n)]

set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_budgetDualCap (n : ℕ) (hn : 2 ≤ n) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 13 / 2) :
    27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) ≤
      2 * (32 * deTurckArmFibreConst n ^ 3 - 28 * deTurckArmFibreConst n ^ 2) := by
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hhalf : 1 / (1 - δ₀) ≤ 2 := by
    rw [div_le_iff₀ h1δ]
    linarith
  have hhalf0 : 0 < 1 / (1 - δ₀) := by positivity
  set f := deTurckArmFibreConst n with hf_def
  have hf0 : 0 ≤ f := deTurckArmFibreConst_nonneg n
  have hf2 : f ^ 2 = (n : ℝ) ^ 3 := sq_deTurckArmFibreConst n
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hf2ge : (8 : ℝ) ≤ f ^ 2 := by
    rw [hf2]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (n : ℝ) ^ 3 := by nlinarith [hn', sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) + 2)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lb : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    have : (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2ub : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.415 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rw [Real.sqrt_sq (by norm_num)] at h
    exact h
  have hfge : 2 * Real.sqrt 2 ≤ f := by
    have h8 : Real.sqrt 8 ≤ Real.sqrt (f ^ 2) := Real.sqrt_le_sqrt hf2ge
    have h8' : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 from by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
    rw [h8', Real.sqrt_sq hf0] at h8
    exact h8
  have hLHS : 27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) =
      27 * c * (Real.sqrt n * n) * ((1 - δ₀) * (1 / (1 - δ₀)) ^ 2) := by
    ring
  rw [rfns_tl_sqrt_mul_self_eq_fibreConst n] at hLHS
  have hδfac : (1 - δ₀) * (1 / (1 - δ₀)) ^ 2 = 1 / (1 - δ₀) := by
    field_simp
  rw [hLHS, hδfac]
  have hstep : 27 * c * f * (1 / (1 - δ₀)) ≤ 54 * c * f := by
    have hcf : 0 ≤ 27 * c * f := by positivity
    calc 27 * c * f * (1 / (1 - δ₀)) ≤ 27 * c * f * 2 :=
          mul_le_mul_of_nonneg_left hhalf hcf
      _ = 54 * c * f := by ring
  refine le_trans hstep ?_
  have hcore : 27 * c ≤ 32 * f ^ 2 - 28 * f := by
    nlinarith [hfge, hs2, hs2lb, hs2ub, hf0, sq_nonneg (f - 2 * Real.sqrt 2)]
  nlinarith [hcore, hf0, mul_nonneg hc0 hf0, hfge, hs2lb, hs2]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
lemma b1_rfns_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (a : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • a) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • a),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a]
  rw [TensorRSSpace.toModel_smul]
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma b1_rfns_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) := by
  rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ P k]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P
      + (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x
        + ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_add]
    rfl]
  refine le_trans (rfns_tl_add_le_sq_sqrt (I := I) (M := M) g₀ 0 (2 + k) x _ _) ?_
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2)
    ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x)]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2)
    ((iteratedCovGrad (I := I) g₀ 0 2 k
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x)]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) P k x]
  set A := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
    ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) with hA_def
  have hA0 : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + k) x _
  have hs : Real.sqrt ((1 / 2 : ℝ) ^ 2 * A) = (1 / 2 : ℝ) * Real.sqrt A := by
    rw [Real.sqrt_mul (by positivity) A]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hs]
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  nlinarith [Real.sqrt_nonneg A]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private lemma b1_unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (A - B) x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          A x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          B x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem b1_appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s
        Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W
      - operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private theorem b1_symmS_eq_self (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
            g₀ 2 S x ![u, w] =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
            g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma b1_metricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
      (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g) x =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x) := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
            g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
private theorem b1_perturbation_eq_metricDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    P = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    b1_symmS_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ =
      ccTensor02Symm (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁ =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₁ -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₀
        from rfl]
    rw [b1_unitModel_sub (I := I) (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₀) x]
    rw [ContinuousMultilinearMap.sub_apply]
    rw [b1_metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      b1_metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
        (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x m =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
          g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x ![m 0, m 1] from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem b1_ccTensor22_ext_of_appCc (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      operatorFieldApply (I := I) (M := M) g₀ 2 2 C W = operatorFieldApply (I := I) (M := M) g₀ 2 2
        D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (operatorFieldApply (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (operatorFieldApply (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
            (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
        (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2

set_option backward.isDefEq.respectTransparency false in
theorem b1_halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) •
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
          (I := I) (M := M) g₀ g₁
        + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
            (I := I) (M := M) g₀ g₁
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := b1_perturbation_eq_metricDifference (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine b1_ccTensor22_ext_of_appCc (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciArmOrder0RiemannHalfBgDiff_appCc_eq_residualFieldSum_add_refoldKernelSecondGrad
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [appCc_smul_left (I := I) (M := M) g₀ 2 2, b1_appCc_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁)) =
      Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁ from rfl]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁
      + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
      (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
          (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.appCc_refoldKernelContractionField
    (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

set_option backward.isDefEq.respectTransparency false in
private lemma b1_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hkey : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
lemma b1_toSection_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    ((A + B).toSection x) = A.toSection x + B.toSection x := by
  rw [SmoothCcTensor.toSection_add]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
lemma b1_toSection_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    ((A - B).toSection x) = A.toSection x - B.toSection x := by
  rw [SmoothCcTensor.toSection_sub]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
lemma b1_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (A : SmoothCcTensor g r s) (x : M) :
    ((c • A).toSection x) = c • A.toSection x := by
  rw [SmoothCcTensor.toSection_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem b1_iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem b1_fixedField_jet_bound (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i F).toSection x) ≤ c i := by
  refine ⟨fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose,
    fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose_spec.1,
    fun i x => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose_spec.2 x⟩

set_option backward.isDefEq.respectTransparency false in
theorem riemannianFiberNormSq_iteratedCovGrad_bgRDiffRefoldRemainderField_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CS, hCS_nn, hCS⟩ :=
    rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualMetricDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨SW, hSW_nn, hSW⟩ := b1_fixedField_jet_bound (I := I) (M := M) g₀ 2 2
    (ccInputSlotSwapField (I := I) (M := M) g₀)
  refine ⟨fun i => 4 * (diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l)
      + 4 * ((1 / 2 : ℝ) ^ 2 * CS i) + 2 * CR i,
    fun i => by
      have h1 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l :=
        mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hCB_nn i')
            (Finset.sum_nonneg fun l _ => hSW_nn l))
      have h2 := hCS_nn i
      have h3 := hCR_nn i
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set w : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hw_def
  have hw_nn : 0 ≤ w := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i + 3)
  have hbg_eq :
    Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁) := rfl
  rw [hbg_eq]
  rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
  rw [b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2
    (2 + i)]
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have hsplit2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x)
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₁
            - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₀)
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w := by
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 2 2
      (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
          (I := I) (M := M) g₀ g₁
        - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
          (I := I) (M := M) g₀ g₀)
      (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
    have hrhs : (diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w =
        diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (CB i' * w) * ∑ l ∈ Finset.range (i + 1 - i'), SW l := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine Finset.sum_le_sum (fun i' hi' => ?_)
    have hi'le : i' ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    have hBGi' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 2 i'
          (Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₁
            - Analysis.Parabolic.TensorSpectral.ricciArmOrder0BackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₀)).toSection x) ≤ CB i' * w := by
      refine le_trans (hCB g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCB_nn i')
      rw [hw_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn
        (by omega) (by omega)
    refine mul_le_mul hBGi' ?_ ?_ (mul_nonneg (hCB_nn i') hw_nn)
    · refine Finset.sum_le_sum (fun l _ => hSW l x)
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
  have hS : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x) ≤
      ((1 / 2 : ℝ) ^ 2 * CS i) * w := by
    rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i (1 / 2)]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 i
          (Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [b1_rfns_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hCS g₁ P htie hδ_le hδ0 hbound i x
  have hR : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) ≤ CR i * w :=
    hCR g₁ P htie hδ_le hδ0 hbound i x
  nlinarith [hsplit2, hA, hS, hR, hw_nn]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma b1_sqrt_rfns_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a + b)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b) := by
  have h := rfns_tl_add_le_sq_sqrt (I := I) (M := M) g r s x a b
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a + b))
      ≤ Real.sqrt ((Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
          + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

set_option backward.isDefEq.respectTransparency false in
lemma b1_sqrt_le_of_le {T B : ℝ} (h : T ≤ B) :
    Real.sqrt T ≤ Real.sqrt B := Real.sqrt_le_sqrt h

set_option backward.isDefEq.respectTransparency false in
lemma b1_sqrt_head_split {e2 btop K w : ℝ} (he2 : 0 ≤ e2) (hbtop : 0 ≤ btop)
    (hK : 0 ≤ K) (hw : 0 ≤ w) {T : ℝ} (hT : T ≤ e2 ^ 2 * btop + K * w) :
    Real.sqrt T ≤ e2 * Real.sqrt btop + Real.sqrt (K * w) := by
  refine le_trans (b1_sqrt_le_of_le hT) ?_
  refine le_trans (b1_sqrt_add_le (e2 ^ 2 * btop) (K * w)
    (by positivity) (by positivity)) ?_
  have h1 : Real.sqrt (e2 ^ 2 * btop) = e2 * Real.sqrt btop := by
    rw [Real.sqrt_mul (by positivity) btop]
    rw [Real.sqrt_sq he2]
  rw [h1]

private lemma b1_sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

set_option backward.isDefEq.respectTransparency false in
lemma b1_young_assembly {T e1 e2 btop K1 K2 K3 K4 K5 w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hK5 : 0 ≤ K5)
    (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ (e1 + e2) * Real.sqrt btop
      + (Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w)
        + Real.sqrt (K4 * w) + Real.sqrt (K5 * w))) :
    T ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop
      + (505 * (K1 + K2 + K3 + K4 + K5)) * w := by
  set u : ℝ := (e1 + e2) * Real.sqrt btop with hu_def
  set v : ℝ := Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w)
    + Real.sqrt (K4 * w) + Real.sqrt (K5 * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := by
    have := Real.sqrt_nonneg (K1 * w)
    have := Real.sqrt_nonneg (K2 * w)
    have := Real.sqrt_nonneg (K3 * w)
    have := Real.sqrt_nonneg (K4 * w)
    have := Real.sqrt_nonneg (K5 * w)
    linarith
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      have huv0 : 0 ≤ u + v := by linarith
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 100) (by norm_num)
  have hu2 : u ^ 2 = (e1 + e2) ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 ≤ 5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w) := by
    have h1 : Real.sqrt (K1 * w) ^ 2 = K1 * w := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (K2 * w) ^ 2 = K2 * w := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (K3 * w) ^ 2 = K3 * w := Real.sq_sqrt (by positivity)
    have h4 : Real.sqrt (K4 * w) ^ 2 = K4 * w := Real.sq_sqrt (by positivity)
    have h5 : Real.sqrt (K5 * w) ^ 2 = K5 * w := Real.sq_sqrt (by positivity)
    have hfive := b1_sq_sum_five_le (Real.sqrt (K1 * w)) (Real.sqrt (K2 * w))
      (Real.sqrt (K3 * w)) (Real.sqrt (K4 * w)) (Real.sqrt (K5 * w))
    rw [h1, h2, h3, h4, h5] at hfive
    simpa only [hv_def] using hfive
  have hone : (1 + (1 / 100 : ℝ)) * u ^ 2 ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop := by
    rw [hu2]
    nlinarith [sq_nonneg (e1 + e2), hbtop]
  have hinv : ((1 : ℝ) / 100)⁻¹ = 100 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 100) * u ^ 2 + (1 + 100) * v ^ 2 := hyoung
    _ ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop
        + (1 + 100) * (5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w)) := by
        have hv2' : (1 + (100 : ℝ)) * v ^ 2 ≤
            (1 + 100) * (5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w)) := by
          nlinarith [hv2]
        linarith [hone, hv2']
    _ = ((201 / 200) * (e1 + e2)) ^ 2 * btop
        + (505 * (K1 + K2 + K3 + K4 + K5)) * w := by ring

end DifferentialGeometry.Analysis.Spectral

end
