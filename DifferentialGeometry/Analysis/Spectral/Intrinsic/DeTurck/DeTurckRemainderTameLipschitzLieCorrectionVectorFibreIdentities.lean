import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionVectorFlatFibreIdentity
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

section LieCorrectionZeroBoundsE2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel cometric_dualTrace_eq_orthoFrame_diag)

omit [SigmaCompactSpace M] in
lemma lieCorrectionZerob_iV_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (reindexCoeffGen (I := I) (M := M) g₀ 3 1
          (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1) lieCorrectionZeroIVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B =
    Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x) B := by
  classical
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x with hV
  set Vf : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) with hVf
  have hchain : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (reindexCoeffGen (I := I) (M := M) g₀ 3 1
          (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1) lieCorrectionZeroIVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B) =
      lieCorrectionZeroTraceStep (I := I) g₁ 1 lieCorrectionZeroIVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
          (reindexCoeffGen (I := I) (M := M) g₀ 3 1
            (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1) lieCorrectionZeroIVPerm)
          (slotExtendIter (I := I) (M := M) g₀ 0 1 2
            (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B) =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 3 1
            (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1) lieCorrectionZeroIVPerm).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 1 2
              (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB)).toSection x) B) from rfl]
    rw [lieCorrectionZerob_KLift_fiber_21 (I := I) (M := M) g₀ (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB) x B]
    rw [← hVf]
    have h := lieCorrectionZerob_traceStep_fiber (I := I) (M := M) g₀ g₁ 1 lieCorrectionZeroIVPerm x
    exact congrFun (congrArg DFunLike.coe h)
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)
  rw [hchain]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  have hLHS : Tensor0SSpace.toModel
      (lieCorrectionZeroTraceStep (I := I) g₁ 1 lieCorrectionZeroIVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)) w =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel B
            ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
          Tensor0SSpace.toModel Vf
            (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) := by
    rw [show lieCorrectionZeroTraceStep (I := I) g₁ 1 lieCorrectionZeroIVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B) =
        cometricDoubleTraceFib (I := I) g₁ 1 x
          (domDomCongrFibRank (I := I) 3 lieCorrectionZeroIVPerm x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)) from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 1 x]
    rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (domDomCongrFibRank (I := I) 3 lieCorrectionZeroIVPerm x
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B))) w]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [domDomCongrFibRank_apply (I := I) 3 lieCorrectionZeroIVPerm x, Tensor0SSpace.toModel_ofModel]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [tensor0SProdKappaFib_apply (I := I) x Vf B, Tensor0SSpace.toModel_ofModel]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · congr 1
      funext k
      fin_cases k <;> rfl
    · congr 1
      funext k
      fin_cases k ; rfl
  rw [hLHS]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel B
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
        Tensor0SSpace.toModel Vf
          (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) =
      (g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V) *
        Tensor0SSpace.toModel B
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] := by
    intro c
    rw [hVf, lieCorrectionZerob_vflat_value (I := I) (M := M) g₀ g₁ gB x
      ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)]
    rw [← hV]
    rw [g₁.symm x V (smoothOrthoFrame (I := I) g₁ x c x)]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hRHS : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V B) w =
      Tensor0SSpace.toModel B (Fin.cons (show E from V) (fun k => (show E from w k))) :=
    lieCorrectionZerob_interior_product_toModel_eval (I := I) (M := M) 1 x V B w
  rw [hRHS]
  have hrepr := lieCorrectionZerob_orthoFrame_center_repr (I := I) (M := M) g₁ x V
  have hexp : Tensor0SSpace.toModel B (Fin.cons (show E from V) (fun k => (show E from w k))) =
      ∑ c : Fin (Module.finrank ℝ E),
        (g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V) *
          Tensor0SSpace.toModel B
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (fun k => (show E from w k))) := by
    have hsum := lieCorrectionZerob_toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel B)
      (Module.finrank ℝ E)
      (fun c => g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V)
      (fun c => ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E))
      (fun k => (show E from w k))
    rw [← hsum]
    exact congrArg (fun t : TangentSpace I x =>
      Tensor0SSpace.toModel B (Fin.cons (show E from t) (fun k => (show E from w k)))) hrepr
  rw [hexp]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  congr 1
  funext k
  fin_cases k <;> rfl

end LieCorrectionZeroBoundsE2

end LieCorrectionZeroBoundsAll

end DifferentialGeometry.Analysis.Spectral

end
