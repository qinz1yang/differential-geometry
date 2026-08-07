import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMixedHalfFibreIdentity
open DifferentialGeometry.Geometry.Connection


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
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

section LieCorr0BoundsAll

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv
  connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel
  metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply
  tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorr0BoundsE3

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel)

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_amix_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
    lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      (2 : ℝ) • (((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2).toSection x) D) +
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg
            (lc0SwapOutPerm * lieCorr0AMixPerm2)).toSection x) D)) := rfl
  rw [h1]
  rw [lc0b_amixhalf_fiber (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2 x D]
  rw [lc0b_amixhalf_fiber (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2) x D]
  rw [← lc0b_swapOut_traceStep (I := I) (M := M) g₁ lieCorr0AMixPerm2 x _]
  rw [show lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D =
      (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D +
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x)
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)) from by
    rw [lieCorr0AMixFib]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]]
  rfl

end LieCorr0BoundsE3

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

