import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionConnectionDifferenceFibreIdentity
open DifferentialGeometry.Geometry.Connection.Realization
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

noncomputable def lieCorrectionZeroTr (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) : SmoothCcTensor g₀ (p + 2) p :=
  reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ p) σ

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lieCorrectionZeroTr_fiber_apply (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) (D : Tensor0SSpace (p + 2) I x) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ p σ).toSection x) D =
    lieCorrectionZeroTraceStep (I := I) g₁ p σ x D := by
  exact congrFun (congrArg DFunLike.coe
    (lieCorrectionZerob_traceStep_fiber (I := I) (M := M) g₀ g₁ p σ x)) D

def lieCorrectionZeroSwapOutPerm : Equiv.Perm (Fin 4) :=
  ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma lieCorrectionZerob_swapOut_traceStep (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) (Z : Tensor0SSpace 4 I x) :
    domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
      (lieCorrectionZeroTraceStep (I := I) g₁ 2 σ x Z) =
    lieCorrectionZeroTraceStep (I := I) g₁ 2 (lieCorrectionZeroSwapOutPerm * σ) x Z := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [domDomCongrFibRank_apply (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show lieCorrectionZeroTraceStep (I := I) g₁ 2 σ x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 σ x Z) from rfl]
  rw [show lieCorrectionZeroTraceStep (I := I) g₁ 2 (lieCorrectionZeroSwapOutPerm * σ) x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 (lieCorrectionZeroSwapOutPerm * σ) x Z) from rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x, cometricDoubleTraceFib_toModel (I := I) g₁ 2
    x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x),
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [domDomCongrFibRank_apply (I := I) 4 σ x Z, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [domDomCongrFibRank_apply (I := I) 4 (lieCorrectionZeroSwapOutPerm * σ) x Z, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  have hpt : ∀ t : Fin 4,
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k)
          (fun j : Fin 2 => w ((Equiv.swap (0 : Fin 2) 1) j))) : Fin 4 → E) t =
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 4 → E) (lieCorrectionZeroSwapOutPerm t) := by
    intro t
    fin_cases t <;> rfl
  rw [hpt (σ i)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroRiemRest_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM
          ((lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x))))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => (lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)))
  intro Y
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorrectionZeroRiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₀ 4 lieCorrectionZeroRiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  refine htr1.congr (fun x => ?_)
  rfl

noncomputable def lieCorrectionZeroRiemRestField (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from TensorRSSpace.ofCLM
          ((lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x))))
      contMDiff_toFun := lieCorrectionZeroRiemRest_contMDiff (I := I) (M := M) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

noncomputable def lieCorrectionZeroInsertionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)
    + reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1)

noncomputable def lieCorrectionZeroVectorBundleField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroVectorBundleTracePermutation)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀))
      (lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀))

noncomputable def lieCorrectionZeroMixedConnectionInnerField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2
      (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀))

noncomputable def lieCorrectionZeroMixedConnectionLiftedField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 6 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
    (slotExtendIter (I := I) (M := M) g₀ 0 3 3
      (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g_bg))
    (lieCorrectionZeroMixedConnectionInnerField (I := I) (M := M) g₀ g₁)

noncomputable def lieCorrectionZeroMixedConnectionOuterField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
    (lieCorrectionZeroMixedConnectionLiftedField (I := I) (M := M) g₀ g₁ g_bg)

noncomputable def lieCorrectionZeroMixedConnectionHalfField (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 2 σlast)
    (lieCorrectionZeroMixedConnectionOuterField (I := I) (M := M) g₀ g₁ g_bg)

noncomputable def lieCorrectionZeroMixedConnectionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • (lieCorrectionZeroMixedConnectionHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
    + lieCorrectionZeroMixedConnectionHalfField (I := I) (M := M) g₀ g₁ g_bg (lieCorrectionZeroSwapOutPerm * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))

noncomputable def lieCorrectionZeroRiemannField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroRiemPerm2) (lieCorrectionZeroRiemRestField (I := I) (M := M) g₀)

end LieCorrectionZeroBoundsE3

end LieCorrectionZeroBoundsAll

end DifferentialGeometry.Analysis.Spectral

end
