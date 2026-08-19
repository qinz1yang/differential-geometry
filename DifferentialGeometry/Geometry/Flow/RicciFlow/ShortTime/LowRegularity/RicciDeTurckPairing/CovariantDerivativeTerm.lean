import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.VectorBundleTerm

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (quartic_product_sum_le_interpolation_square
  one_le_one_add_pow_four pow_four_le_one_add_pow_four sq_le_one_add_pow_four
  three_term_sq_le_weighted_product)
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance (x : M) :
    ContinuousAdd (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd

private lemma half_sq_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (s / 2) ^ 2 ≤ 1 := by
  nlinarith

private lemma unit_interval_sq_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    s ^ 2 ≤ 1 := by
  nlinarith

private lemma one_le_one_add_sq {A : ℝ} (hA : 0 ≤ A) :
    1 ≤ (1 + A) ^ 2 := by
  nlinarith

private lemma sq_le_one_add_sq {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ (1 + A) ^ 2 := by
  nlinarith

theorem exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hbdd⟩ := lie_omega_sobolev_two_bound (I := I) (M := M) hDim g
  exact ⟨B, hB, fun gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 =>
    hbdd gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3⟩

theorem exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ := lieOmega_pair_h2 (I := I) (M := M) hDim g
  exact ⟨B0, B1, hB0, hB1,
    fun gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3 =>
      hpair gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3⟩


theorem exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
        ((Module.finrank ℝ E : ℝ) * B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hwSelf⟩ := exists_metricLoweredConnectionDifference_covariantJetNormSq_bound (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hbase : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) =
      connectionDifferenceSection (I := I) gT g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gT).symm
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Bs R * A) ^ 2 := by
    rw [hbase, connSec_self_h2 (I := I) (M := M) g gT]
    exact hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) :=
      covariantJetNormSq_bilinearSlotInsertionCoefficient_two_le (I := I) (M := M) g (connectionDifferenceEndomorphism (I := I) (M := M) g gT)
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * Bs R * A) ^ 2 := by ring

theorem exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) ≤
        ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
          (Module.finrank ℝ E : ℝ) * B1 R * D2 +
          (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hbT : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) =
      connectionDifferenceSection (I := I) gT g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gT).symm
  have hbU : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gU) =
      connectionDifferenceSection (I := I) gU g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gU).symm
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) ≤
      (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
    rw [hbT, hbU]
    exact hpair gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) =
      covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
            connectionDifferenceEndomorphism (I := I) (M := M) g gU)) := by
      rw [DifferentialGeometry.Analysis.Sobolev.armSlotEndoCc_sub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
              connectionDifferenceEndomorphism (I := I) (M := M) g gU)) :=
      covariantJetNormSq_bilinearSlotInsertionCoefficient_two_le (I := I) (M := M) g _
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) := by
      rw [DifferentialGeometry.Analysis.Sobolev.armSlotEndoCc_sub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
        (Module.finrank ℝ E : ℝ) * B1 R * D2 +
        (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannCurvatureCoefficientField_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    riemannCurvatureCoefficientField (I := I) (M := M) g T - riemannCurvatureCoefficientField (I := I) (M := M) g U =
      riemannCurvatureCoefficientField (I := I) (M := M) g (T - U) := by
  simp only [riemannCurvatureCoefficientField, riemannCurvatureCoefficientField]
  rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_right]
  module

theorem exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 T := by
  obtain ⟨C₀, hC₀, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 2 4
  refine ⟨2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionA (I := I) (M := M) g) +
      C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionB (I := I) (M := M) g)), ?_, ?_⟩
  · have h1 : 0 ≤ C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionA (I := I) (M := M) g) :=
      mul_nonneg hC₀ (covariantJetNormSq_nonneg (I := I) (M := M) g _)
    have h2 : 0 ≤ C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionB (I := I) (M := M) g) :=
      mul_nonneg hC₀ (covariantJetNormSq_nonneg (I := I) (M := M) g _)
    linarith
  intro T
  rw [riemannCurvatureCoefficientField]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) T +
          ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) T) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) T) +
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) T)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
            (riemannLoweredContractionA (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2 T +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2
            (riemannLoweredContractionB (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2 T) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (happ _ T) (happ _ T)) (by norm_num)
    _ = 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
          (riemannLoweredContractionA (I := I) (M := M) g) +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2
          (riemannLoweredContractionB (I := I) (M := M) g)) *
        covariantJetNormSq (I := I) (M := M) g 2 T := by ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le
    (g : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g 0 4) {K : ℝ}
    (hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ K)
    (hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ K) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) X + X +
          domDomCongrSection (I := I) g lrPermA Y +
          domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) Y +
          domDomCongrSection (I := I) g lrPermB Y +
          domDomCongrSection (I := I) g lrPermC Y) ≤ 94 * K :=
  covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hX) hX
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hY) (by rw [covariantJetNormSq_domDomCongrSection]; exact hY)
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hY) (by rw [covariantJetNormSq_domDomCongrSection]; exact hY)

theorem exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
              covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  refine ⟨94 * Ca, by positivity, ?_⟩
  intro gm
  have hQB : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gm) ≤
      Ca * (covariantJetNormSq (I := I) (M := M) g 2
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
    rw [connectionDifferenceQuadraticPairedTensor]
    refine (happ _ _).trans (le_of_eq ?_)
    ring
  have hQA : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm) ≤
      Ca * (covariantJetNormSq (I := I) (M := M) g 2
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
    rw [connectionDifferenceQuadraticComposedTensor]
    refine (happ _ _).trans (le_of_eq ?_)
    rw [covariantJetNormSq_domDomCongrSection]
    ring
  rw [connectionDifferenceQuadraticCurvatureTerm]
  refine (covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le (I := I) (M := M) g _ _ hQB hQA).trans (le_of_eq ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceQuadraticPairedTensor_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) := by
  simp only [connectionDifferenceQuadraticPairedTensor,
    connectionDifferenceEndomorphism, connectionDifferenceMetricLoweredTensor]
  rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceQuadraticComposedTensor_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
              connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU)) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  simp only [connectionDifferenceQuadraticComposedTensor,
    connectionDifferenceEndomorphism, connectionDifferenceMetricLoweredTensor]
  rw [domDomCongrSection_sub, operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

theorem exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
              connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                    (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
              covariantJetNormSq (I := I) (M := M) g 2
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  refine ⟨188 * Ca, by positivity, ?_⟩
  intro gT gU
  have hQBd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) ≤
      2 * Ca * (covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
    rw [connectionDifferenceQuadraticPairedTensor_sub]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
        connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU)
    have e2 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)
    linarith
  have hQAd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) ≤
      2 * Ca * (covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
    rw [connectionDifferenceQuadraticComposedTensor_sub]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
          connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU))
    have e2 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT))
    rw [covariantJetNormSq_domDomCongrSection] at e1
    rw [covariantJetNormSq_domDomCongrSection] at e2
    linarith
  have hsplit : connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
          (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) +
        (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermA
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermB
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermC
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) := by
    simp only [connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticPairedTensor,
      connectionDifferenceQuadraticPairedTensor, connectionDifferenceQuadraticComposedTensor, connectionDifferenceQuadraticComposedTensor, domDomCongrSection_sub]
    abel_nf
  rw [hsplit]
  refine (covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le (I := I) (M := M) g _ _ hQBd hQAd).trans (le_of_eq ?_)
  ring


theorem exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Cc, hCc, hcurv⟩ := exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquad⟩ := exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  let D : ℝ → ℝ := fun R =>
    2 * Cc + 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2)
  refine ⟨D, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    simp only [D]
    linarith
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := unit_interval_sq_le_one hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hCF : covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * A ^ 2 :=
    (hcurv T).trans (mul_le_mul_of_nonneg_left
      ((covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) T).trans hT3)
      hCc)
  have harm : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhat : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm) ≤ (Bt R * A) ^ 2 :=
    hhatb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hQF : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) :=
    (hquad gm).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul harm hhat (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (sq_nonneg _)) hCq)
  have hdecomp : deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s =
      (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
        (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm := by
    rw [hgm, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := half_sq_le_one hs.1 hs.2
  have hu0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T) := covariantJetNormSq_nonneg (I := I) (M := M) g _
  have hfin : 2 * (Cc * A ^ 2 +
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) ≤ D R * (1 + A) ^ 4 := by
    have e1 : Cc * A ^ 2 ≤ Cc * (1 + A) ^ 4 :=
      mul_le_mul_of_nonneg_left (sq_le_one_add_pow_four hA) hCc
    have e2 : Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) ≤
        Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4) := by
      refine mul_le_mul_of_nonneg_left ?_ hCq
      have hre : (fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2 =
          (fr * Bs R) ^ 2 * (Bt R) ^ 2 * A ^ 4 := by ring
      rw [hre]
      exact mul_le_mul_of_nonneg_left (pow_four_le_one_add_pow_four hA)
        (by positivity)
    have heq : D R * (1 + A) ^ 4 =
        2 * (Cc * (1 + A) ^ 4) +
          2 * (Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4)) := by
      simp only [D]
      ring
    rw [heq]
    linarith
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
          (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T) +
        covariantJetNormSq (I := I) (M := M) g 2
          ((-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) +
        (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) := by
      rw [covariantJetNormSq_smul, covariantJetNormSq_smul]
    _ ≤ 2 * (Cc * A ^ 2 +
        Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * A ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
            1 * covariantJetNormSq (I := I) (M := M) g 2
              (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hu0
        rw [one_mul] at hle
        exact hle.trans hCF
      have h2 : (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
          Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) =
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) := by ring
        rw [hvv]
        exact hQF
      linarith
    _ ≤ D R * (1 + A) ^ 4 := hfin

theorem exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cc, hCc, hcurv⟩ := exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquadp⟩ := exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨A0, A1, hA0, hA1, harmp⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hhatp⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let Mh : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Ma : ℝ → ℝ := fun R =>
    2 * (fr * A0 R + fr * A1 R) ^ 2 + 2 * (fr * A1 R) ^ 2
  let Kq : ℝ → ℝ := fun R =>
    (fr * Bs R) ^ 2 * Mh R + Ma R * (Bt R) ^ 2
  let C : ℝ → ℝ := fun R => 2 * Cc + 2 * (Cq * Kq R)
  have hMh : ∀ R : ℝ, 0 ≤ R → 0 ≤ Mh R := fun R hR => by
    simp only [Mh]
    positivity
  have hMa : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ma R := fun R hR => by
    simp only [Ma]
    positivity
  have hKq : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kq R := fun R hR => by
    have h1 : (0 : ℝ) ≤ (fr * Bs R) ^ 2 * Mh R :=
      mul_nonneg (sq_nonneg _) (hMh R hR)
    have h2 : (0 : ℝ) ≤ Ma R * (Bt R) ^ 2 :=
      mul_nonneg (hMa R hR) (sq_nonneg _)
    simp only [Kq]
    linarith
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ Cq * Kq R := mul_nonneg hCq (hKq R hR)
    simp only [C]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := unit_interval_sq_le_one hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (T - U)).trans hTU3
  set pl2 : ℝ := (1 + A) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    exact one_le_one_add_sq hA
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_sq hA
  have hd0 : (0 : ℝ) ≤ D3 ^ 2 := sq_nonneg _
  have hquart : pl2 * (pl2 * D3 ^ 2) = (1 + A) ^ 4 * D3 ^ 2 := by
    rw [hpl2]
    ring
  have hCFd : covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T -
        riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
    rw [riemannCurvatureCoefficientField_sub]
    exact (hcurv (T - U)).trans (mul_le_mul_of_nonneg_left hTU2 hCc)
  have harmU : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gmU Q hQsymm hQtie hδ_le hδ0 hδQ hδZ R A hR hA hQ2 hQ3
  have hhatT : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤ (Bt R * A) ^ 2 :=
    hhatb gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhatD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
        connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤ Mh R * (pl2 * D3 ^ 2) := by
    refine (hhatp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ R A D3 D3 hR hA hD3 hD3
      hP2 hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact three_term_sq_le_weighted_product hpl21 hplA2 hd0 le_rfl
  have harmD : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤
      Ma R * (pl2 * D3 ^ 2) := by
    refine (harmp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ R A D3 D3 hR hA hD3 hD3
      hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact three_term_sq_le_weighted_product hpl21 hplA2 hd0 le_rfl
  have hQFd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
        connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) ≤
      Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
    refine (hquadp gmT gmU).trans ?_
    have e1 : covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤
        (fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmU hhatD
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) (sq_nonneg _)
      refine hstep.trans ?_
      have hre : (fr * Bs R * A) ^ 2 * (Mh R * (pl2 * D3 ^ 2)) =
          (fr * Bs R) ^ 2 * Mh R * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (sq_nonneg _) (hMh R hR))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have e2 : covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmD hhatT
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg (hMa R hR) (mul_nonneg hpl20 hd0))
      refine hstep.trans ?_
      have hre : Ma R * (pl2 * D3 ^ 2) * (Bt R * A) ^ 2 =
          Ma R * (Bt R) ^ 2 * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (hMa R hR) (sq_nonneg _))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have hsum : Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) =
        Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
      simp only [Kq]
      ring
    calc
      Cq * (_ + _) ≤ Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
          Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCq
      _ = Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := hsum
  have hdecomp : deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
      deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s =
      (-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) +
        (-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
          connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) := by
    rw [hgmT, hgmU, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s,
      deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g U hδU hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := half_sq_le_one hs.1 hs.2
  have hcf0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T -
        riemannCurvatureCoefficientField (I := I) (M := M) g U) := covariantJetNormSq_nonneg (I := I) (M := M) g _
  have hDenv : D3 ^ 2 ≤ (1 + A) ^ 4 * D3 ^ 2 := by
    calc D3 ^ 2 = 1 * D3 ^ 2 := (one_mul _).symm
      _ ≤ (1 + A) ^ 4 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right (one_le_one_add_pow_four hA) hd0
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) +
          (-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U)) +
        covariantJetNormSq (I := I) (M := M) g 2
          ((-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU))) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) +
        (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) := by
      rw [covariantJetNormSq_smul, covariantJetNormSq_smul]
    _ ≤ 2 * (Cc * D3 ^ 2 + Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T -
              riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤
            1 * covariantJetNormSq (I := I) (M := M) g 2
              (riemannCurvatureCoefficientField (I := I) (M := M) g T -
                riemannCurvatureCoefficientField (I := I) (M := M) g U) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hcf0
        rw [one_mul] at hle
        exact hle.trans hCFd
      have h2 : (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) ≤
          Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
              connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) =
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
                connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) := by ring
        rw [hvv]
        exact hQFd
      linarith
    _ ≤ C R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have e1 : Cc * D3 ^ 2 ≤ Cc * ((1 + A) ^ 4 * D3 ^ 2) :=
        mul_le_mul_of_nonneg_left hDenv hCc
      have heq : C R * ((1 + A) ^ 4 * D3 ^ 2) =
          2 * (Cc * ((1 + A) ^ 4 * D3 ^ 2)) +
            2 * (Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
        simp only [C]
        ring
      rw [heq]
      linarith

noncomputable def deTurckLieCovariantDerivativeRemainderPairTrace
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
    (slotExtendIter (I := I) (M := M) g 0 4 2
      (deTurckLieCovariantDerivativeRemainderTensor
        (I := I) (M := M) g T hδT hδZ s))

theorem exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderPairTrace
            (I := I) (M := M) g T hδT hδZ s) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Dr, hDr, hr4⟩ := exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Dr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hDr R hR), ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  unfold deTurckLieCovariantDerivativeRemainderPairTrace
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) := rfl
  have hbase := hr4 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) =
      covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
      rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
    _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Dr R * (1 + A) ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Dr R * (1 + A) ^ 4 := by ring

theorem exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderPairTrace
              (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderPairTrace
              (I := I) (M := M) g U hδU hδZ s) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cr, hCr, hr4p⟩ := exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Cr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hCr R hR), ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  unfold deTurckLieCovariantDerivativeRemainderPairTrace
  have hXsub :
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) =
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [← rsDomDomCongrSection_sub, slotExtend_sub, slotExtend_sub]
    rfl
  have hbase := hr4p T U hT hU hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 hs
  rw [hXsub, covariantJetNormSq_rsDomDomCongrSection]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
      mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Cr R * ((1 + A) ^ 4 * D3 ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Cr R * ((1 + A) ^ 4 * D3 ^ 2) := by ring

omit [BoundarylessManifold I M] in
theorem deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s =
      deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
        g T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] s := rfl

theorem exists_deTurckLieCovariantDerivativeRemainder_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Dx, hDx, hcovb⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Cip, hCip, hinterp⟩ := covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  let Bh : ℝ → ℝ := fun R => 2 * (Ca * Cp ^ 2 * Dx R + Ca * Bp ^ 2 * Cx R)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := by
    intro R hR
    have h1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
    have h2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
    simp only [Bh]
    linarith
  refine ⟨min ρp ρb, B0, B1, lt_min hρp hρb,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hT3i : covariantJetNormSq (I := I) (M := M) g 3 T ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp T R A4 hR hA4 hT2 hT4
  have hU3i : covariantJetNormSq (I := I) (M := M) g 3 U ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp U R A4 hR hA4 hU2 hU4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hpl4 : (0 : ℝ) ≤ pl2 * pl2 := mul_nonneg hpl20 hpl20
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg D3]
  have hUT :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gmT g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gmU g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g T hδT hδZ s,
    deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [htel, covariantJetNormSq_smul, neg_one_sq, one_mul]
  have hPairD : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hPQn hCp) 2
  have hPairU : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ Bp ^ 2 :=
    hlcvb Q gmU hQtie hQnb
  have hXT : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
      Dx R * (pl2 * pl2) := by
    refine (hcovb T hT hδ_le hδ0 hδT hδZ R a hR ha0 hT2 hT3i hs).trans
      (le_of_eq ?_)
    rw [hpl2]
    ring
  have hXD : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((pl2 * pl2) * D3 ^ 2) := by
    refine (hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ R a D3 hR ha0 hD3
      hT2 hU2 hT3i hU3i hTU3 hs).trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hc1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
  have hc2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
  have hT1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))) ≤
      Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairD hCa) hXT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * (Cp * N) ^ 2 * (Dx R * (pl2 * pl2)) =
        Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * N ^ 2) := by ring
      _ ≤ Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNu hpl4) hc1
  have hT2b : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairU hCa) hXD
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * Bp ^ 2 * (Cx R * ((pl2 * pl2) * D3 ^ 2)) =
        Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * D3 ^ 2) := by ring
      _ ≤ Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD3le hpl4) hc2
  have hwhole : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Bh R * ((pl2 * pl2) * u) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ + _) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
            covariantJetNormSq (I := I) (M := M) g 2 _) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) +
          Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u)) := by
        linarith [hT1, hT2b]
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hwhole.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact quartic_product_sum_le_interpolation_square (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
