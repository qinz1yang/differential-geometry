import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTraceFibreIdentities
open DifferentialGeometry.Analysis.Spectral


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorrectionZeroCore
open DifferentialGeometry.PDE.RicciFlow
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

section LieCorrectionZeroBoundsAll

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckVectorFieldCovariantDerivativeEndomorphism deTurckVectorFieldCovariantDerivativeEndomorphism_apply deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff deTurckVFCovDeriv
  connectionDifferenceOp_homSection_contMDiff metricConnectionDifferenceLoweredFib metricConnectionDifferenceLoweredFib_toModel
  metricConnectionDifferenceLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply
  tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorrectionZeroBoundsE3

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel)

omit [SigmaCompactSpace M] in
lemma lieCorrectionZerob_vb_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroVectorBundleField (I := I) (M := M) g₀ g₁).toSection x) D =
    lieCorrectionZeroVBFib (I := I) g₀ g₁ x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroVectorBundleField (I := I) (M := M) g₀ g₁).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroVectorBundleTracePermutation).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1
            (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
            (lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D))) := rfl
  rw [h1]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D from
    lieCorrectionZerob_iV_fiber (I := I) (M := M) g₀ g₁ g₀ x D]
  rw [lieCorrectionZerob_KLift_fiber_13 (I := I) (M := M) g₀ (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀) x _]
  rw [lieCorrectionZerob_kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  have h2 := lieCorrectionZerob_traceStep_fiber (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroVectorBundleTracePermutation).toSection x)
      (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) =
      lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x
        (tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)) from
    congrFun (congrArg DFunLike.coe h2) _]
  rw [show lieCorrectionZeroVBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • (lieCorrectionZeroTraceStep (I := I) g₁ 2 lieCorrectionZeroVectorBundleTracePermutation x
        ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x))
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) from by
    rw [lieCorrectionZeroVBFib]
    rw [ContinuousLinearMap.smul_apply]
    rfl]

end LieCorrectionZeroBoundsE3

end LieCorrectionZeroBoundsAll

end DifferentialGeometry.Analysis.Spectral

end
