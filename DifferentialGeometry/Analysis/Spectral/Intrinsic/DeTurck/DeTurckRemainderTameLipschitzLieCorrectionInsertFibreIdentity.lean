import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionRiemannFibreIdentity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


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

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lieCorrectionZerob_insert_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel (lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D) m := by
  have hsplit : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) := rfl
  rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g_bg x D m]
  have hterm1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) m =
      Tensor0SSpace.toModel D
        (Function.update m 0 (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x (m 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) =
        slotInsertEndoFib (I := I) (M := M) 2 0 x
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x) D from rfl]
    rw [slotInsertEndoFib_apply_eval]
  have hterm2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel D
        (Function.update m 1 (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x (m 1))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x _ D]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) =
        tensorRS_domDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
      ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) =
        slotInsertEndoFib (I := I) (M := M) 2 0 x
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
      (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x
            ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
          ((Equiv.swap (0 : Fin 2) 1) k))
        = Function.update m 1 (lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x (m 1)) := by
      funext k
      have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
      have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
      simp only [Function.update_apply]
      rw [hswap0, Equiv.swap_apply_self]
      have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
        apply propext
        constructor
        · intro h
          have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
          rwa [Equiv.swap_apply_self, hswap0] at h2
        · intro h
          rw [h, hswap1]
      simp only [hcond]
    rw [harg]
  rw [hterm1, hterm2]

end LieCorrectionZeroBoundsE3

end LieCorrectionZeroBoundsAll

end DifferentialGeometry.Analysis.Spectral

end
