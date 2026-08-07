import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionKappaFibreIdentities
open DifferentialGeometry.Analysis.Spectral
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

section LieCorr0BoundsE2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel cometric_dualTrace_eq_orthoFrame_diag)

def lc0IVPerm : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2

noncomputable def lc0VFlat (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (lc0PureDT (I := I) (M := M) g₀ g₁ 1)
    (lc0Kappa (I := I) (M := M) g₀ g₁ gB)

lemma lc0b_vflat_value (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (u : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
          (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => u) =
      g₁.inner x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x) u := by
  have hfib : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) from rfl]
    rw [ContinuousLinearMap.comp_apply]
    rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ gB x]
    rfl
  rw [hfib]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 1 x]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x))
    (fun _ : Fin 1 => u)]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (fun _ : Fin 1 => u))) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x
        (smoothOrthoFrame (I := I) g₁ x c x) (smoothOrthoFrame (I := I) g₁ x c x)) u := by
    intro c
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x]
    rfl
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  rw [PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gB x]
  rw [map_sum, ContinuousLinearMap.sum_apply]

end LieCorr0BoundsE2

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end


