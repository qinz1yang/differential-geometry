import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTraceFibreIdentities
open DifferentialGeometry.Analysis.Spectral


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

lemma lc0b_vb_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0VBField (I := I) (M := M) g₀ g₁).toSection x) D =
    lieCorr0VBFib (I := I) g₀ g₁ x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0VBField (I := I) (M := M) g₀ g₁).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
            (lc0IVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D))) := rfl
  rw [h1]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D from
    lc0b_iV_fiber (I := I) (M := M) g₀ g₁ g₀ x D]
  rw [lc0b_KLift_fiber_13 (I := I) (M := M) g₀ (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) x _]
  rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  have h2 := lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm x
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) =
      lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)) from
    congrFun (congrArg DFunLike.coe h2) _]
  rw [show lieCorr0VBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • (lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x))
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) from by
    rw [lieCorr0VBFib]
    rw [ContinuousLinearMap.smul_apply]
    rfl]

end LieCorr0BoundsE3

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end
