import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Coefficients.ConnectionInsertionFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.MixedTensorFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.MixedTensorSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.SecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.FixedConnectionSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.FirstOrderBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.EndomorphismInsertion.TopOrderSeparation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.Coefficient.Decomposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.VectorBundle.Expansion

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Spectral.MetricRealization

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

theorem connSec_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
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
            ‖iteratedCovGrad (I := I) g₀ 1 2 i
              (connectionDifferenceSection (I := I) g₁ g₀)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := connectionDifference_grid_unif (I := I) (M := M) hδ₀
  obtain ⟨B, hB, hlow⟩ := h1_low_uniform
    (I := I) (M := M) hDim gBase hΛ (r := 1) (s := 2) C hC
  refine ⟨B, hB, ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  refine hlow g₀ hEq hjet1 hjet2 P
    (connectionDifferenceSection (I := I) g₁ g₀) R hR hP ?_
  intro i _ x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₀ g₁ P htie hδ_le hδ_nonneg hbound i x

theorem insert_h1_uniform
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
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gBase -
                lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
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
  let BA : ℝ → ℝ := fun R => CA * BC R * BO R
  let Q : ℝ → ℝ := fun R =>
    4 * (Module.finrank ℝ E : ℝ) * (BA R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hF
  have hBA : ∀ R : ℝ, 0 ≤ R → 0 ≤ BA R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCA (hBC R hR)) (hBO R hR)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie δ hδ_le hδ_nonneg hbound
    R hR hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let Fix : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase -
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₀
  let OD : SmoothCcTensor g₀ 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ -
      deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase
  let AD : SmoothCcTensor g₀ 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ -
      deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gBase
  let SD : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ gBase)
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr] using
      htr g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        (Equiv.refl _) R hR hP
  have hFixEq : Fix = metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase := by
    dsimp only [Fix]
    rw [connLow_self_zero (I := I) g₀, sub_zero]
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ F ^ 2 := by
    rw [hFixEq]
    calc
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
      deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g₀ g₁ g₀ gBase
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
  have hADform :
      AD = ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD := by
    dsimp only [AD, OD]
    unfold deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference
    calc
      operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) -
          operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase) =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) -
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase) := by
          exact congrArg₂ (fun X Y => X - Y)
            (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2
              (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)).symm
            (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2
              (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase)).symm
      _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ -
            deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase) :=
        (operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gBase)).symm
  have hAD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤ (BA R) ^ 2 := by
    rw [hADform]
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
    simpa only [BA, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hraise_sub :
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ -
            deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gBase) =
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) -
          cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gBase) := by
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
  have hSDform :
      SD = cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [SD, AD, endoDiffSection]
    rw [slotInsertEndoCc_sub, connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise,
      connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise, ← hraise_sub]
  have hSD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) ≤ (BA R) ^ 2 := by
    rw [hSDform]
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ (BA R) ^ 2 := hAD
  have hraw :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gBase -
            lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [SD] using
          normSq_iteratedCovGrad_lieCorrectionZeroInsertionDiff_le
            (I := I) (M := M) g₀ g₁ gBase i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) * (BA R) ^ 2 :=
      mul_le_mul_of_nonneg_left hSD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B R) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ R), Q]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
