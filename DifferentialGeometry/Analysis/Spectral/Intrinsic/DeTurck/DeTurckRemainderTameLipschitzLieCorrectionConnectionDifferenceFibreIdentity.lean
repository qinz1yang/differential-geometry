import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionVectorFibreIdentities
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


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

noncomputable def lc0NEndoSec (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ⟨fun x : M => lieCorr0NEndo (I := I) g₀ g₁ g_bg x,
    lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg⟩

noncomputable def lc0IVField (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
    (reindexCoeffGen (I := I) (M := M) g₀ 3 1
      (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2 (lc0VFlat (I := I) (M := M) g₀ g₁ gB))

noncomputable def lc0CdVField (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 1 (lc0IVField (I := I) (M := M) g₀ g₁ gB)
    (connDiffSection (I := I) g₁ g₀)

lemma lc0b_cdV_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om =
    slotInsertEndoFib (I := I) (M := M) 1 0 x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x)) om := by
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x with hV
  have hstep : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V
        (connDiffFib (I := I) g₁ g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0IVField (I := I) (M := M) g₀ g₁ gB).toSection x)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffSection (I := I) g₁ g₀).toSection x) om) from rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om from rfl]
    exact lc0b_iV_fiber (I := I) (M := M) g₀ g₁ gB x
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om)
  rw [hstep]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [lc0b_interior_product_toModel_eval (I := I) (M := M) 1 x V
    (connDiffFib (I := I) g₁ g₀ x om) w]
  rw [slotInsertEndoFib_apply_eval]
  have hLHS : Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
      (Fin.cons (show E from V) (fun k => (show E from w k))) =
      om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) := by
    rw [show Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
        (Fin.cons (show E from V) (fun k => (show E from w k))) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om)
          (Fin.cons V (fun k => w k)) from rfl]
    rw [connDiffFib_apply_eval (I := I) g₁ g₀ x om (Fin.cons V (fun k => w k))]
    congr 1
  rw [hLHS]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om
    (Function.update (fun k => (show E from w k)) 0
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x V ((fun k => (show E from w k)) 0)))]
  rw [Function.update_self]
  rw [show (om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) : ℝ) =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) from
    (cotangentToDual_apply (I := I) om _).symm]

end LieCorr0BoundsE2

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end


