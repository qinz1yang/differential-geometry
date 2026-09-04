import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.ProductTwoTerm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JointSmoothness
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Bilinear
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.RawComponentBound
import DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RawComponentIdentification
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.ChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.InverseMetricDifferenceCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.CurvatureCoefficientField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.Realization.Section
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.OperatorField.Application
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.PathIntegralFibreNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.PrincipalCoefficientBackgroundJetBounds
import DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ContinuousRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartLieDerivative
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDerivative.RemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieCoefficientApplication
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.ChartComponents
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.SecondOrderTerm.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.TameEstimates
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature (chartRiemannTensor)
open DifferentialGeometry.Integral.DivergenceTheorem
  (extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_operatorFieldApplication_eq pathIntegralCoeffField_toSection linearizedRicciCovariantJetJointSmoothness
  linearizedRicciCovariantJetJointContinuity linearizedRicciCovariantJetJointSmoothness_zero
  exists_linearizedRicci_covariantJet_coeffFields ricciTensor_realize_sub_eq_covariantJet_operatorFieldApply
  linearizedRicciOrderZeroField linearizedRicciFirstOrderField linearizedRicciSecondOrderFieldLichnerowicz
  linearizedRicciOrderZeroBaseCoeff linearizedRicciOrderZeroCorrectionField linearizedRicciFirstOrderBaseCoeff
  linearizedRicciFirstOrderCorrectionField ricciDeTurckPrincipalCoefficient traceHessianCoeff
  linearizedRicci_orderZeroField_jointSmooth linearizedRicci_firstOrderField_jointSmooth
  linearizedRicci_secondOrderFieldLichnerowicz_jointSmooth ricciFirstOrderKoszulCoeff
  exists_firstOrderKoszul_metricPerturbationPath_riemannianFiberNormSq_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local operatorFieldApplication_zero_left_local ccTensor02Symm
  ccTensor02Symm_sub smoothCcTensorBilinForm_ccTensor02Symm iteratedCovGrad_ccTensor02Symm_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPathDomain metricPerturbationPathDomain_isOpen Icc_subset_metricPerturbationPathDomain linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum
  hasDerivAt_realizedRicciChartSum metricPerturbationPath)
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
  (deTurckLieSecondOrderPrincipalCoeff deTurckLieFirstOrderCoeff deTurckLieCoeffField
  deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jointSmooth deTurckLieFirstOrderCoeff_metricPerturbationPath_jointSmooth
  deTurckLieCoeffField_metricPerturbationPath_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoefficientInputSlots reindexCoefficientInputSlotsFiber reindexCoefficientInputSlotsFiber_apply reindexCoefficientInputSlots_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieSecondOrderDivSlotPermA
  deTurckLieSecondOrderDivSlotPermAT traceHessianCoeff_toSection)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma dim1_smul_rep (h1 : Module.finrank ℝ E = 1) (e : E) (he : e ≠ 0) (v : E) :
    ∃ c : ℝ, c • e = v :=
  exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := E) h1 he v

omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_domDomCongr_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) (ρ : Equiv.Perm (Fin d)) :
    ContinuousMultilinearMap.domDomCongr ρ f = f := by
  classical
  have hpos : 0 < Module.finrank ℝ E := h1 ▸ Nat.one_pos
  set b := Module.finBasis ℝ E with hb
  set e : E := b ⟨0, hpos⟩ with he_def
  have he : e ≠ 0 := b.ne_zero _
  apply ContinuousMultilinearMap.ext
  intro v
  have hrep : ∀ i : Fin d, ∃ c : ℝ, c • e = v i := fun i => dim1_smul_rep h1 e he (v i)
  choose c hc using hrep
  have hv : v = fun i => c i • e := by
    funext i
    exact (hc i).symm
  rw [ContinuousMultilinearMap.domDomCongr_apply, hv]
  have hL : (f fun i => c (ρ i) • e) = (∏ i, c (ρ i)) • f (fun _ => e) :=
    f.map_smul_univ (fun i => c (ρ i)) (fun _ => e)
  have hR : (f fun i => c i • e) = (∏ i, c i) • f (fun _ => e) :=
    f.map_smul_univ c (fun _ => e)
  rw [hL, hR, Equiv.prod_comp ρ c]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dim1_slotPermCLM_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (x : M) (D : Tensor0SBundle.Tensor0SSpace d I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x D = D := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply]
  rw [dim1_domDomCongr_eq h1 (Tensor0SBundle.Tensor0SSpace.toModel D) ρ]
  exact Tensor0SBundle.Tensor0SSpace.ofModel_toModel (𝕜 := ℝ) D

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
      (I := I) g₁ x = 0 := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM]
  have hF : ∀ ρ₁ ρ₂ ρ₃ : Equiv.Perm (Fin 4),
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₁ x)
        + (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₂ x)
        - DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x
        - (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₃ x)
        = 0 := by
    intro ρ₁ ρ₂ ρ₃
    apply ContinuousLinearMap.ext
    intro Z
    rw [sub_apply, sub_apply,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [dim1_slotPermCLM_eq (I := I) h1 ρ₁ x Z, dim1_slotPermCLM_eq (I := I) h1 ρ₂ x Z,
      dim1_slotPermCLM_eq (I := I) h1 ρ₃ x Z]
    rw [zero_apply]
    abel
  rw [hF]
  rw [smul_zero]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero
    (h1 : Module.finrank ℝ E = 1) (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CoeffField
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw
    [Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CoeffField_toSection]
  change
    (Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CometricTracedCLM
      (I := I) g₀ g₁ x) = _
  rw
    [Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CometricTracedCLM]
  rw [ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (I := I) h1 g₁ x]
  rw [ContinuousLinearMap.zero_comp]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma dim1_riemannOp_first_two_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x)
    (hw : w ≠ 0) :
    DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x v w u = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := TangentSpace I x)
    (show Module.finrank ℝ (TangentSpace I x) = 1 from h1) hw v
  have hself : DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x w w u = 0 := by
    have hsw := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x w w u
    have h2 : (2 : ℝ) • (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x w w u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hsw]
      abel
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    exact (smul_eq_zero.mp h2).resolve_left h2ne
  rw [← hc]
  rw [(DifferentialGeometry.Geometry.Curvature.riemannOp
    (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x).map_smul c w]
  rw [smul_apply, smul_apply]
  rw [hself, smul_zero]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma dim1_smoothOrthoFrame_ne_zero (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Geometry.Connection.smoothOrthoFrame (I := I) g₁ x a x ≠ 0 := by
  intro h0
  have horth := DifferentialGeometry.Geometry.Connection.smoothOrthoFrame_orthonormal_at_center
    (I := I) g₁ x a a
  rw [if_pos rfl] at horth
  rw [h0] at horth
  rw [map_zero] at horth
  exact one_ne_zero horth.symm

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma dim1_ricciOrderZeroRiemannCoeff_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection]
  change (Tensor0SBundle.TensorRSSpace.ofCLM
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib (I := I) g₁ x)) = _
  have hfib : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib
      (I := I) g₁ x = 0 := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib]
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
    apply ContinuousMultilinearMap.ext
    intro v
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel]
    have hz : ∀ a b : Fin (Module.finrank ℝ E),
        (g₁.inner x) (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
            (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame (I := I) g₁ x a x)
            (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame (I := I) g₁ x b x))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) *
          D.toModel ![
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame
                (I := I) g₁ x a x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame
                (I := I) g₁ x b x)] = 0 := by
      intro a b
      rw [dim1_riemannOp_first_two_eq_zero (I := I) h1 g₁ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)) _ _
        (dim1_smoothOrthoFrame_ne_zero (I := I) g₁ x a)]
      rw [map_zero, zero_apply, zero_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hz a b))]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, mul_zero]
    have : (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.TensorRSSpace 2 2 I x) D)) v = 0 := by
      change (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) D)) v = 0
      rw [zero_apply]
      rw [show (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        (0 : Tensor0SBundle.Tensor0SSpace 2 I x)) = 0 from map_zero _]
      rfl
    rw [this]
  rw [hfib]
  rfl

end DifferentialGeometry.Analysis.Spectral

end
