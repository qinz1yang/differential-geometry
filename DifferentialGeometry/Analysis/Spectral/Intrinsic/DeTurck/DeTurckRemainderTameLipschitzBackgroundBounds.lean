import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradSectionPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricDifferenceSlotCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmOperatorFieldApplication
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckPrincipalCoefficientBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPathChartLieDerivative
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffOperatorFieldApplicationValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm2CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzRicciArmCoeffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLiePathValueDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieArmChartValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrectionTameBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmDiffL2TameBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzMetricPrincipalDefectTotalCurvatureFold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzDegenerateOneDimensionalVanishing
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_operatorFieldApplication_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_operatorFieldApply
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciDeTurckPrincipalCoefficient traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_metricPerturbationPath_riemannianFiberNormSq_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local operatorFieldApplication_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPathDomain metricPerturbationPathDomain_isOpen Icc_subset_metricPerturbationPathDomain linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum jointContMDiff_toModel_continuous_slice
  hasDerivAt_realizedRicciChartSum_general metricPerturbationPath)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_operatorFieldApplication_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
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
  (lieDeTurckChartSlope deriv_metricPerturbationPath_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField
  deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointSmooth deTurckLieArm1Coeff_metricPerturbationPath_jointSmooth
  deTurckLieCoeffField_metricPerturbationPath_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA
  deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem)
open Analysis.Parabolic.TensorSpectral

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
lemma de_turck_arm_fibre_const_eq_one_of_finrank_eq_one (h1 : Module.finrank ℝ E = 1) :
    deTurckArmFibreConst (Module.finrank ℝ E) = 1 := by
  rw [h1]
  rw [deTurckArmFibreConst]
  rw [Nat.cast_one, one_pow, Real.sqrt_one]

set_option backward.isDefEq.respectTransparency false in
private lemma sqrt_natCast_mul_natCast_eq_deTurckArmFibreConst (n : ℕ) :
    Real.sqrt n * n = deTurckArmFibreConst n := by
  rw [deTurckArmFibreConst]
  rw [show ((n : ℝ)) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 from by ring]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [Real.sqrt_sq (Nat.cast_nonneg n)]

set_option backward.isDefEq.respectTransparency false in
lemma background_coefficient_le_deTurckArmFibreConst_polynomial (n : ℕ) (hn : 2 ≤ n) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 13 / 2) :
    27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) ≤
      2 * (32 * deTurckArmFibreConst n ^ 3 - 28 * deTurckArmFibreConst n ^ 2) := by
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hhalf : 1 / (1 - δ₀) ≤ 2 := by
    rw [div_le_iff₀ h1δ]
    linarith
  have hhalf0 : 0 < 1 / (1 - δ₀) := by positivity
  set f := deTurckArmFibreConst n with hf_def
  have hf0 : 0 ≤ f := de_turck_arm_fibre_const_nonneg n
  have hf2 : f ^ 2 = (n : ℝ) ^ 3 := sq_de_turck_arm_fibre_const n
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
  rw [sqrt_natCast_mul_natCast_eq_deTurckArmFibreConst n] at hLHS
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
    [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
private lemma unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
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
    [SigmaCompactSpace M] in
private theorem operatorFieldApplication_sub_left_ext (g : SmoothRiemannianMetric I M) (r s : ℕ)
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
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem ccTensor02Symm_eq_self (g₀ : SmoothRiemannianMetric I M)
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
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma metricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
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
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem eq_metricDifferenceCcTensor_of_inner_add (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    P = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    ccTensor02Symm_eq_self (I := I) (M := M) g₀ P hPsymm
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
    rw [unitModel_sub (I := I) (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₀) x]
    rw [ContinuousMultilinearMap.sub_apply]
    rw [metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
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
    [SigmaCompactSpace M] in
private theorem ccTensor22_ext_of_operatorFieldApplication (g₀ : SmoothRiemannianMetric I M)
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
theorem half_ricciArmOrder0RiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction
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
        + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
            (I := I) (M := M) g₀ g₁
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.decompositionKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := eq_metricDifferenceCcTensor_of_inner_add (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine ccTensor22_ext_of_operatorFieldApplication (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciArmOrder0RiemannHalfBackgroundDiff_operatorFieldApplication_eq_residualFieldSum_add_decompositionKernelSecondGrad
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [operatorFieldApplication_smul_left (I := I) (M := M) g₀ 2 2, operatorFieldApplication_sub_left_ext (I := I) (M := M) g₀ 2 2]
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
      Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
        (I := I) (M := M) g₀ g₁ from rfl]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁
      + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
        (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.decompositionKernelContractionField
      (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
          (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldApplication_decompositionKernelContractionField
    (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

set_option backward.isDefEq.respectTransparency false in
theorem riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le
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
              (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BackgroundRCommCoeffDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CS, hCS_nn, hCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmSharpGradKoszulResidualMetricDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨SW, hSW_nn, hSW⟩ := DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound (I := I) (M := M) g₀ 2 2
    (ccInputSlotSwapField (I := I) (M := M) g₀)
  refine ⟨fun i => 4 * (diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l)
      + 4 * ((1 / 2 : ℝ) ^ 2 * CS i) + 2 * CR i,
    fun i => by
      have h1 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l :=
        mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
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
    Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
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
  rw [DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply
      (I := I) (M := M) g₀ (r := 2) (s := 2 + i),
    DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply
      (I := I) (M := M) g₀ (r := 2) (s := 2 + i)]
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
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
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
    rw [DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i (1 / 2)]
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
    rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _]
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

end DifferentialGeometry.Analysis.Spectral

end
