import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Tensor.RSTensor.ParametricSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.GramDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormRawComponentBound
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricDifferenceSlotCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceSymmetrizedReindexedCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ThreeArm.OperatorField.Application
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckPrincipalCoefficientBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartLieDerivative
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffOperatorFieldApplicationValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.GramDerivativeChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.ArmOne.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.ArmTwo.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.TameEstimates
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.ConnectionLaplacianJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.RicciArmCoefficientBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LiePathDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LieArmChartValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LieThreeArmDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrectionTameBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.ArmDifferencePathIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Defs
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
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero linearizedRicciThreeArmHjoint_smul_add
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
  realizedRicciChartSum
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_background_operatorFieldApplication_eq_zero_of_slot01Symm
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (hWsymm : ∀ (x : M) (u₀ u₁ u₂ u₃ : E),
      unitModel (I := I) (M := M) g₀ 4 W x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 W x ![u₁, u₀, u₂, u₃]) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricDoubleTraceCoefficient
              (I := I) (M := M) g₀ g₀) W = 0 := by
  classical
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_zero, zero_apply]
  rw [deTurckMetricPrincipalDefectTotal, operatorFieldApplication_sub_left, operatorFieldApplication_sub_left, operatorFieldApplication_add_left, operatorFieldApplication_add_left]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add,
    sub_apply, sub_apply, add_apply, add_apply]
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_apply_eq
      (I := I) g₀ g₀ W x v
  have hTHraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq
      (I := I) (M := M) g₀ g₀ W x v
  have hRACraw :=
    Analysis.Parabolic.TensorSpectral.ricciDeTurckPrincipalCoefficient_operatorFieldApplication_eq_combinedTrace
      (I := I) (M := M) g₀ g₀ W x v
  have hPure :=
    Analysis.Parabolic.TensorSpectral.cometricDoubleTraceCoefficient_operatorFieldApplication_eq_roughLaplacian
      (I := I) (M := M) g₀ g₀ W x v
  have hTH : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₀) W) x
        v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![v 0, v 1,
            cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
    rw [hTHraw]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
      (by funext i; fin_cases i <;> rfl)
  have hRAC : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀)
        W) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              ![cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, v 1, (Module.finBasis ℝ E) k]
          + ∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 4 W x
                ![cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  v 1, v 0, (Module.finBasis ℝ E) k])
        - ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v))) := by
    rw [hRACraw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine congrArg₂ (fun a b : ℝ => a - b) (congrArg₂ (fun a b : ℝ => a + b) ?_ ?_) rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
  rw [hLie, hTH, hRAC, hPure]
  have hswapA : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 0,
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 1, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 0, v 1, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 0)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 1) ((Module.finBasis ℝ E) k)
  have hswapB : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 1,
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 0, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 1, v 0, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 1)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 0) ((Module.finBasis ℝ E) k)
  rw [hswapA, hswapB]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deTurckMetricPrincipalDefectTotal_metricPerturbationPath_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointSmooth
      (I := I) g₀ T T' hδ hδ'
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add (I := I) (r := 4) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := jointTotalSpaceRS_sub (I := I) (r := 4) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq (I := I) (M := M)
    g₀ T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

def deTurckPhiTotPathIntegral (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
    (fun s => deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
    (metricPerturbationPathDomain (δ := δ) (δ' := δ')) metricPerturbationPathDomain_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)
    (by
      have h := deTurckMetricPrincipalDefectTotal_metricPerturbationPath_jointSmooth
        (I := I) (M := M) g₀ T T' hδ hδ'
      rw [linearizedRicciThreeArmHjoint] at h
      exact h)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (lieDeTurckChartSlope deriv_metricPerturbationPath_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField
  deTurckLieArm2PrincipalCoeff_metricPerturbationPath_jointSmooth deTurckLieArm1Coeff_metricPerturbationPath_jointSmooth
  deTurckLieCoeffField_metricPerturbationPath_jointSmooth)

theorem deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
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
            v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2
                (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛCr, hΛCr_nn, hC0r⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Br, hBr_nn, hJr⟩ :=
    linearizedRicciArm_concreteField_jetL2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨ΛL0, hΛL0_nn, hL0r⟩ :=
    deTurckLieCoeffField_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛLc, hΛLc_nn, hLcr⟩ :=
    lieCorrectionZeroField_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛL1, hΛL1_nn, hL1r⟩ :=
    deTurckLieArm1Coeff_metricPerturbationPath_riemannianFiberNormSq_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P0, hP0_nn, hP0j⟩ :=
    deTurckLieCoeffField_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨PL, hPL_nn, hPLj⟩ :=
    lieCorrectionZeroField_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P1, hP1_nn, hP1j⟩ :=
    deTurckLieArm1Coeff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨max (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc)) (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)),
    max (Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)))
      (Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i)),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w = smoothCcTensorBilinForm (I := I) g₀
        (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub (I := I) (M := M) g₀ T T' x v w,
      ccTensorBilin_sub (I := I) (M := M) g₀ T T' x w v, hTsymm x v w, hT'symm x v w]
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt
  have hSopen : IsOpen (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := metricPerturbationPathDomain_isOpen
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorrectionZeroField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg) with hΨ₀def
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg with hΨ₁def
  set Ψ₂ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) with hΨ₂def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀ (δ := δ) (δ' := δ') := by
    rw [hΨ₀def]
    exact linearizedRicciThreeArmHjoint_smul_add (I := I) (M := M) g₀ 2 (-2 : ℝ) _ _
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieCoeffField_add_deTurckLieRemainderField_metricPerturbationPath_jointSmooth (I := I) g₀ T T' hδ
        hδ' g_bg)
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁ (δ := δ) (δ' := δ') := by
    rw [hΨ₁def]
    exact linearizedRicciThreeArmHjoint_smul_add (I := I) (M := M) g₀ 3 (-2 : ℝ) _ _
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieArm1Coeff_metricPerturbationPath_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψ₂ (δ := δ) (δ' := δ') := by
    rw [hΨ₂def]
    exact deTurckMetricPrincipalDefectTotal_metricPerturbationPath_jointSmooth (I := I) (M := M) g₀ T T' hδ hδ'
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₂ t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψ₂
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hj2 x
  set C₀ : SmoothCcTensor g₀ 2 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
    (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj0 with hC₀def
  set C₁ : SmoothCcTensor g₀ 3 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
    (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj1 with hC₁def
  have hPitop : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  refine ⟨C₀, C₁, ?_, ?_, ?_, ?_, ?_⟩
  · apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    let vt : Fin 2 → TangentSpace I x := fun i =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
    rw [hPitop]
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) g₀ 2 _ _ x, sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) x) v =
        deTurckRicciRHS (I := I) g_bg g₁ x (vt 0) (vt 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x) v =
        deTurckRicciRHS (I := I) g_bg g₁' x (vt 0) (vt 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') rfl x v]
    have hsplit : ∀ (g : SmoothRiemannianMetric I M),
        deTurckRicciRHS (I := I) g_bg g x (vt 0) (vt 1) =
          ((-2 : ℝ) • ricciTensor (I := I) g x (vt 0) (vt 1)) +
            lieDerivMetricClm (I := I) g
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (vt 0) (vt 1) := by
      intro g
      rw [deTurckRicciRHS, add_apply, add_apply,
        smul_apply, smul_apply]
      rfl
    rw [hsplit g₁, hsplit g₁']
    rw [show ((-2 : ℝ) • ricciTensor (I := I) g₁ x (vt 0) (vt 1) +
            lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (vt 0) (vt 1)) -
          ((-2 : ℝ) • ricciTensor (I := I) g₁' x (vt 0) (vt 1) +
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (vt 0) (vt 1)) =
        ((-2 : ℝ) • (ricciTensor (I := I) g₁ x (vt 0) (vt 1) -
            ricciTensor (I := I) g₁' x (vt 0) (vt 1))) +
          (lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (vt 0) (vt 1) -
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (vt 0) (vt 1)) from by
      simp only [smul_sub]; ring]
    rw [hg₁, hg₁']
    rw [ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1)]
    rw [lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1)]
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add
      ((DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_intervalIntegrable
        (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1)).const_mul (-2 : ℝ))
      (linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1))]
    have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
        (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) s
          + linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) s =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      rw [MeasureTheory.ae_iff]
      have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
      refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
      rw [Set.mem_ofPred_eq, Classical.not_imp] at hs
      obtain ⟨hsmem, hsneq⟩ := hs
      rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
      refine hsneq ?_
      have hRid : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) s =
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
      have hLid := linearizedDeTurckLieAt_eq_threeArm_of_symm (I := I) (M := M)
        g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hSsymm hsIoo x v
      have hRid' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) s =
          unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hRid, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply]
      have hLid' : linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) s =
          unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorrectionZeroField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hLid, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply]
      have e0 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorrectionZeroField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v := by
        simp only [hΨ₀def]
        rw [operatorFieldApplication_add_left, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply,
          operatorFieldApplication_smul_left,
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, smul_apply,
          smul_eq_mul]
      have e1 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v := by
        simp only [hΨ₁def]
        rw [operatorFieldApplication_add_left, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply,
          operatorFieldApplication_smul_left,
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, smul_apply,
          smul_eq_mul]
      have e2 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        simp only [hΨ₂def]
        rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul (I := I) (M := M)
          g₀ T T' hδ hδ' s]
        rw [operatorFieldApplication_add_left, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply,
          operatorFieldApplication_smul_left,
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, smul_apply,
          smul_eq_mul]
      rw [hRid', hLid', e0, e1, e2]
      ring
    rw [intervalIntegral.integral_congr_ae hintegrand]
    have hI0 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_operatorFieldApplication_intervalIntegrable_tame (I := I) g₀ 2 Ψ₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) hSI hc0 x v
    have hI1 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_operatorFieldApplication_intervalIntegrable_tame (I := I) g₀ 3 Ψ₁
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) hSI hc1 x v
    have hI2 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_operatorFieldApplication_intervalIntegrable_tame (I := I) g₀ 4 Ψ₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) hSI hc2 x v
    rw [intervalIntegral.integral_add (hI0.add hI1) hI2, intervalIntegral.integral_add hI0 hI1]
    have he0 := pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
    have he1 := pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g₀ 3 2 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
    have he2 := pathIntegralCoeffField_operatorFieldApplication_eq (I := I) (M := M) g₀ 4 2 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
    rw [← hC₀def] at he0
    rw [← hC₁def] at he1
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply, he0, he1, he2]
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Ψ₀ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₀def]
      have hadd := lieCorrectionZerob_riemannianFiberNormSq_toSection_add_le (I := I) (M := M) g₀ 2 2
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg
          + lieCorrectionZeroField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := le_sq_of_sqrt_le
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).1)
      have haddL := lieCorrectionZerob_riemannianFiberNormSq_toSection_add_le (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg)
        (lieCorrectionZeroField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hL0 := hL0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      have hLc := hLcr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Ψ₀
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj0 x
      (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc))
      ((hc0 x).mono (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)) hsup
    rw [← hC₀def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Ψ₁ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₁def]
      have hadd := lieCorrectionZerob_riemannianFiberNormSq_toSection_add_le (I := I) (M := M) g₀ 3 2
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := le_sq_of_sqrt_le
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).2.1)
      have hL1 := hL1r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Ψ₁
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hj1 x
      (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1))
      ((hc1 x).mono (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)) hsup
    rw [← hC₁def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) :=
        Finset.sum_nonneg fun i _ => by
          have := hP0_nn i; have := hPL_nn i; linarith
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg Br)) hsum
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Ψ₀ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₀def]
      have htow := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorrectionZeroField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul, norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).1 s hs
      have htowL := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
        (lieCorrectionZeroField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P0 i :=
        Finset.sum_le_sum fun i hi =>
          hP0j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hcsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), PL i :=
        Finset.sum_le_sum fun i hi =>
          hPLj T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hexpand : (∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) =
          4 * (∑ i ∈ Finset.range (a + 1), P0 i) + 4 * (∑ i ∈ Finset.range (a + 1), PL i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      linarith only [htow, hsc, hRj, htowL, hLsum, hcsum, hexpand]
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 2 a Ψ₀ hSI hSopen hj0
      hjet
    rw [← hC₀def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_nonneg fun i _ => hP1_nn i
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg Br))
        (mul_nonneg (by norm_num) hsum)
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Ψ₁ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₁def]
      have htow := jetTowerSum_add_le (I := I) g₀ 3 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul, norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).2.1 s hs
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_le_sum fun i hi =>
          hP1j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      linarith only [htow, hsc, hRj, hLsum]
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 3 a Ψ₁ hSI hSopen hj1
      hjet
    rw [← hC₁def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : SmoothCcTensor g₀ 2 4,
      ∀ S : SmoothCcTensor g₀ 0 2,
        iteratedCovGrad (I := I) g₀ 0 2 2 S
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I)
                g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C S := by
  classical
  refine ⟨⟨⟨fun y : M =>
      (show Tensor0SBundle.TensorRSSpace 2 4 I y from
        TensorRSSpace.ofCLM (curvatureOperatorOnTensorFib (I := I) (M := M) g₀ 2 y)),
      slotFreeCurvOpFib_contMDiff (I := I) (M := M) g₀ 2⟩,
    HasCompactSupport.of_compactSpace _⟩, ?_⟩
  intro S
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) g₀ 4 _ _ x, sub_apply,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel (I := I)
      g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) x,
    ContinuousMultilinearMap.domDomCongr_apply]
  let vt : Fin 4 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (vt 0), smoothExtensionTangent_contMDiff (I := I) x (vt 0)⟩
    with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (vt 1), smoothExtensionTangent_contMDiff (I := I) x (vt 1)⟩
    with hYs_def
  have hXx : Xs x = vt 0 := smoothExtensionTangent_eq (I := I) x (vt 0)
  have hYx : Ys x = vt 1 := smoothExtensionTangent_eq (I := I) x (vt 1)
  set m : Fin 2 → TangentSpace I x := ![vt 2, vt 3] with hm_def
  let mE : Fin 2 → E := fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)
  have hv_eq : v = fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((Fin.cons (Xs x) (Fin.cons (Ys x) m) : Fin 4 → TangentSpace I x) i) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> simp [vt]
  have hv_swap : (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((Fin.cons (Ys x) (Fin.cons (Xs x) m) : Fin 4 → TangentSpace I x) i) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def, vt]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) mE := by
    conv_lhs => rw [hv_eq]
    rw [unitModel]
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
    rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
    simpa only [mE, Tensor0SSpace.toModel_apply_tangent] using
      tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
        Xs.contMDiff Ys.contMDiff x m
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) mE := by
    rw [hv_swap]
    rw [unitModel]
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
    rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
    simpa only [mE, Tensor0SSpace.toModel_apply_tangent] using
      tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
        Ys.contMDiff Xs.contMDiff x m
  have h3 : tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x -
      tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
        (fun y : M => S.toSection y) x =
      riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x :=
    tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g₀ 0 2
      (fun y : M => S.toSection y)
      ((Xs.contMDiff x).mdifferentiableAt (by simp))
      ((Ys.contMDiff x).mdifferentiableAt (by simp))
  have h4 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) mE -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) mE =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) mE := by
    simp only [mE, Tensor0SSpace.toModel_apply_tangent]
    have h3eval := congrArg
      (fun L : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x =>
        Tensor0SSpace.eval (L (unitZeroSec (I := I) (M := M) x)) m) h3
    simpa only [sub_apply, Tensor0SSpace.eval_sub] using h3eval
  have h5 := riemannSec_tensorCov_apply_eval (I := I) (M := M) g₀ 0 2 Xs Ys
    S.toSection (unitZeroSec (I := I) (M := M)) x mE
  have h6 : riemannSec
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀))
      (fun b => Xs b) (fun b => Ys b) (fun b => unitZeroSec (I := I) (M := M) b) x = 0 :=
    riemannSec_tensor0SCov_zero_eq_zero (I := I) g₀ Xs Ys
      (fun b => unitZeroSec (I := I) (M := M) b) (contMDiff_unitZeroSection (I := I) (M := M)) x
  have h7 := riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g₀ 2 Xs Ys
    (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
      (unitZeroSec (I := I) (M := M) b))
    (contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x m
  have h8 : ∀ u : TangentSpace I x, baseSlotCurv (I := I) g₀ Xs Ys x u =
      riemannOp (LeviCivita (I := I) g₀) x (vt 0) (vt 1) u := by
    intro u
    rw [show baseSlotCurv (I := I) g₀ Xs Ys x u =
        riemannSec (LeviCivita (I := I) g₀) (fun b => Xs b) (fun b => Ys b)
          (fun b => smoothExtensionTangent (I := I) x u b) x from rfl]
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g₀) Xs.contMDiff Ys.contMDiff
      (smoothExtensionTangent_contMDiff (I := I) x u)]
    rw [smoothExtensionTangent_eq (I := I) x u, hXx, hYx]
  have h9 := slotFreeCurvOpFib_apply_eval (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x)) (vt 0) (vt 1) m
  have hv0 : v = fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((Fin.cons (vt 0) (Fin.cons (vt 1) m) : Fin 4 → TangentSpace I x) i) := by
    rw [hm_def]
    funext i
    fin_cases i <;> simp [vt]
  rw [h1, h2, h4, h5, h6, map_zero]
  simp only [mE, Tensor0SSpace.toModel_apply_tangent]
  rw [Tensor0SSpace.eval_zero, sub_zero, h7]
  rw [Finset.sum_congr rfl (fun k _ => by rw [h8 (m k)])]
  rw [← h9]
  conv_rhs => rw [unitModel, hv0, Tensor0SSpace.toModel_apply_tangent,
    operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_deTurckMetricPrincipalDefectTotal_background_curvatureFold_of_symm
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ K₀ : SmoothCcTensor g₀ 2 2,
      ∀ (S : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ S x v w = smoothCcTensorBilinForm (I := I) g₀ S x w v)
            →
        operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricDoubleTraceCoefficient
                  (I := I) (M := M) g₀ g₀)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          operatorFieldApply (I := I) (M := M) g₀ 2 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
  classical
  obtain ⟨C24, hC24⟩ :=
    exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff (I := I) (M := M) g₀
  refine ⟨(1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricDoubleTraceCoefficient
          (I := I) (M := M) g₀ g₀) C24, ?_⟩
  intro S hSsymm
  set Φd : SmoothCcTensor g₀ 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricDoubleTraceCoefficient
          (I := I) (M := M) g₀ g₀ with hΦd_def
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hW_def
  set Wsw : SmoothCcTensor g₀ 0 4 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 1) W with hWsw_def
  have hsplit : W = (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) := by
    have h : (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) =
        ((1/2 : ℝ) + (1/2 : ℝ)) • W + ((1/2 : ℝ) - (1/2 : ℝ)) • Wsw := by
      rw [smul_add, smul_sub, add_smul, sub_smul]
      abel
    rw [h]
    norm_num
  have hsym : ∀ (x : M) (u₀ u₁ u₂ u₃ : E),
      unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₁, u₀, u₂, u₃] := by
    intro x u₀ u₁ u₂ u₃
    have hv : ∀ a b : E,
        (fun i => (![a, b, u₂, u₃] : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) i)) =
          ![b, a, u₂, u₃] := by
      intro a b
      funext i
      fin_cases i <;> rfl
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) (M := M) g₀ 4 W Wsw x,
      add_apply, add_apply,
      hWsw_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel
        (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) W x,
      ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      hv u₀ u₁, hv u₁ u₀]
    exact add_comm _ _
  have hkill : operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw)) = 0 := by
    rw [operatorFieldApplication_smul_right, hΦd_def,
      deTurckMetricPrincipalDefectTotal_background_operatorFieldApplication_eq_zero_of_slot01Symm (I := I) (M := M) g₀
        (W + Wsw) hsym, smul_zero]
  calc operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd W
      = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
          ((1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw)) := by rw [← hsplit]
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw))
        + operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) :=
      operatorFieldApplication_add_right (I := I) (M := M) g₀ 4 2 Φd _ _
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) := by
      rw [hkill, zero_add]
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd (W - Wsw) :=
      operatorFieldApplication_smul_right (I := I) (M := M) g₀ 4 2 (1/2 : ℝ) Φd _
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C24 S) := by
      rw [hW_def, hWsw_def, hW_def, hC24 S]
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [operatorFieldComposition_zero_eq_operatorFieldApply,
        operatorFieldApply_assoc]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [operatorFieldApplication_smul_left (I := I) (M := M) g₀ 2 2 (1/2 : ℝ) _ S]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24)
        (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
      rw [iteratedCovGrad_zero]

end DifferentialGeometry.Analysis.Spectral

end
