import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.ConnectionInsertionFirstOrderBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLow_self_zero
    (g : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifferenceCoefficient (I := I) g g = 0 := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  change unitModel (I := I) (M := M) g 3
      (metricLoweredConnectionDifferenceCoefficient (I := I) g g) x m = 0
  rw [show m = fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)) by
    funext i
    exact (tangentSpaceModelContinuousLinearEquiv (I := I) x).apply_symm_apply (m i)]
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  rw [PDE.DeTurck.connectionDifference_self]
  simp

private theorem norm_add_sq_le
    {V : Type*} [SeminormedAddCommGroup V] (u v : V) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (‖u‖ - ‖v‖)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem dom_h1_eq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    (∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 s q
          (domDomCongrSection (I := I) g σ S)‖ ^ 2) =
      ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 s q S‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem raise_sub
    (g : SmoothRiemannianMetric I M) (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W -
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply]
  simp only [cometricRaiseSlot0Field_toSection]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private theorem wAlphaB_sub_eq_ccOperatorFieldComp
    (g₀ g₁ gA gB : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA -
        deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA -
          deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB) := by
  unfold deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference
  calc
    operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA) -
        operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB) := by
      exact congrArg₂ (fun X Y => X - Y)
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA)).symm
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB)).symm
    _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA -
          deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB) :=
      (operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA)
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB)).symm


theorem exists_uniform_deTurckLieCovariantDerivativeInsertion_backgroundDifference_covariantJetNormSq_one_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ R : ℝ, 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gBase -
                deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
            (B R) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Bt, hBt, htr⟩ := trace_h2_uniform
    (I := I) (M := M) 1 hDim gBase hΛ0 hδ₀
  obtain ⟨CO, hCO, hoprod⟩ := operatorFieldComposition_h2_h2_to_h2_uniform_bound
    (I := I) (M := M) hDim gBase hΛ 0 3 1
  obtain ⟨BC, hBC, hc⟩ := connSec_h1_uniform
    (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨CA, hCA, haprod⟩ := operatorFieldComposition_h1_uniform_bound
    (I := I) (M := M) hDim gBase hΛ 0 1 2
  obtain ⟨F, hF, hfix⟩ := connFix_h2_uniform
    (I := I) (M := M) hDim gBase hΛ
  let BO : ℝ → ℝ := fun R => CO * Bt R * F
  let BAB : ℝ → ℝ := fun R => CA * BC R * BO R
  let Q : ℝ → ℝ := fun R =>
    4 * (Module.finrank ℝ E : ℝ) *
      (2 * ((BO R) ^ 2 + (BAB R) ^ 2))
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hF
  have hBAB : ∀ R : ℝ, 0 ≤ R → 0 ≤ BAB R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCA (hBC R hR)) (hBO R hR)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie δ hδ_le hδ_nonneg hbound
    R hR hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let Fix : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₀ -
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase
  let OD : SmoothCcTensor g₀ 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase -
      deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀
  let AA : SmoothCcTensor g₀ 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ gBase -
      deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g₀
  let AB : SmoothCcTensor g₀ 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gBase -
      deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀
  let AD : SmoothCcTensor g₀ 0 2 :=
    deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ gBase -
      deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g₀
  let WD : SmoothCcTensor g₀ 1 1 :=
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ gBase -
      deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g₀
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr] using
      htr g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        (Equiv.refl _) R hR hP
  have hFixEq : Fix = -metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase := by
    dsimp only [Fix]
    rw [connLow_self_zero (I := I) g₀, zero_sub]
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ F ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hFixEq, iteratedCovGrad_neg, norm_neg]
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection
          (I := I) (M := M) g₀ gBase i]
      _ ≤ F ^ 2 := hfix g₀ hEq hjet1 hjet2 hjet3
  have hODform :
      OD = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 Tr Fix := by
    simpa only [OD, Tr, Fix] using
      deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g₀ g₁ gBase g₀
  have hOD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hODform]
    simpa only [BO] using
      hoprod g₀ hEq hjet1 hjet2 Tr Fix (Bt R) F
        (hBt R hR) hF hTr hFix
  have hCAjet : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (BC R) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ i]
      _ ≤ (BC R) ^ 2 :=
        hc g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound R hR hP
  have hAAform :
      AA = domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g₀ 0 1 OD) := by
    dsimp only [AA, OD]
    unfold deTurckVectorFieldCovariantDerivativeLoweredBase
    rw [covGrad_sub,
      DifferentialGeometry.Analysis.Sobolev.domDomCongrSection_sub]
  have hAA : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hAAform, dom_h1_eq]
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ]
        nlinarith [sq_nonneg ‖OD‖]
      _ ≤ (BO R) ^ 2 := hOD
  have hAB : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) ≤ (BAB R) ^ 2 := by
    dsimp only [AB, OD]
    rw [wAlphaB_sub_eq_ccOperatorFieldComp (I := I) (M := M)]
    have hnorm := haprod g₀ hEq hjet1 hjet2
      (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD
      (BC R) (BO R) (hBC R hR) (hBO R hR) hCAjet hOD
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD⟩ :
            SmoothCcTensorH1 g₀ 0 2))
      hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 0 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD)] at hsquare
    simpa only [BAB, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hADform : AD = AA + AB := by
    dsimp only [AD, AA, AB]
    unfold deTurckVectorFieldCovariantDerivativeLowered
    abel
  have hAD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤
        2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) := by
        rw [hADform]
        apply Finset.sum_le_sum
        intro i _
        rw [iteratedCovGrad_add]
        exact norm_add_sq_le _ _
      _ = 2 * (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2) +
          2 * (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (BO R) ^ 2 + 2 * (BAB R) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hAA (by norm_num))
          (mul_le_mul_of_nonneg_left hAB (by norm_num))
      _ = 2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by ring
  have hWDform :
      WD = cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [WD, AD]
    rw [deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered,
      deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered, ← raise_sub]
  have hWD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) ≤
        2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by
    rw [hWDform]
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ 2 * ((BO R) ^ 2 + (BAB R) ^ 2) := hAD
  have hraw :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gBase -
            deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [WD] using
          normSq_iteratedCovGrad_deTurckLieCovariantDerivativeInsertion_backgroundDifference_le (I := I) (M := M) g₀ g₁ gBase g₀ i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (2 * ((BO R) ^ 2 + (BAB R) ^ 2)) :=
      mul_le_mul_of_nonneg_left hWD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B R) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ R), Q]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
