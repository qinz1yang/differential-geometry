import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.ZeroOrderCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.FirstOrderCoefficient
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CovariantTensorApplicationBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopPathDeviationBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Topology DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem top_pair_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ W : SmoothCcTensor g 0 2,
          let Φ := rhsTopPathIntegral (I := I) (M := M) g T T'
              hδ_lt hδ hδ'_lt hδ' -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 W).toFun
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2 W)).toFun| ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 := by
  classical
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    top_path_dev_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C : ℝ := Cdev * h2CovsumC K.rankTwo
  refine ⟨ρ, C, hρ, mul_nonneg hCdev (h2CovsumC_nonneg K.rankTwo), ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' W
  let Φ : SmoothCcTensor g 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g T T'
        hδ_lt hδ hδ'_lt hδ' -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  obtain ⟨hΦ, _⟩ := hdev g hEq hjet T T' hδ_lt hδ hδ'_lt hδ'
    hR hRρ hT hT'
  have hact : IsCurvAction0 (I := I) (M := M) g 2 K.rankTwo :=
    (hK.bounds g hEq hjet).1
  have hpair := operator_field_application_second_covariant_derivative_pairing_h2_bound (I := I) (M := M) g hact
    (mul_nonneg hCdev hR) Φ (by simpa only [Φ] using hΦ) W
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2 W).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2 W)).toFun| ≤
      C * R * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2
  calc
    _ ≤ (Cdev * R) * h2CovsumC K.rankTwo *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 := hpair
    _ = C * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 := by
      simp only [C]
      ring

theorem top_pair_h4_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ U : SmoothCcTensor g 0 2,
          let Φ := rhsTopPathIntegral (I := I) (M := M) g T T'
              hδ_lt hδ hδ'_lt hδ' -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hpair⟩ :=
    top_pair_h2_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  have h := hpair g hEq hjet T T' hδ_lt hδ hδ'_lt hδ'
    hR hRρ hT hT'
    (oneMinusConnLapSmooth (I := I) g 0 2 U)
  have hshift :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (oneMinusConnLapSmooth (I := I) g 0 2 U)‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 2 U).symm
  rwa [hshift] at h

theorem top_pair_h5_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ U : SmoothCcTensor g 0 2,
          let Φ := rhsTopPathIntegral (I := I) (M := M) g T T'
              hδ_lt hδ hδ'_lt hδ' -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
          |tensorL2Inner (I := I) (M := M) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ ^ 2 := by
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    top_path_dev_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h23_uniform (I := I) (M := M) hDim gBase hΛ
  let C : ℝ := Capp * Cdev
  refine ⟨ρ, C, hρ, mul_nonneg hCapp hCdev, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  let W : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 U
  let Φ : SmoothCcTensor g 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g T T'
        hδ_lt hδ hδ'_lt hδ' -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let A : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Φ
      (iteratedCovGrad (I := I) g 0 2 2 W)
  obtain ⟨_, hΦ⟩ := hdev g hEq hjet T T' hδ_lt hδ hδ'_lt hδ'
    hR hRρ hT hT'
  have hA :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A‖ ≤
        Capp * (Cdev * R) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ := by
    simpa only [A, Φ] using happ g hEq hjet Φ W (Cdev * R)
      (mul_nonneg hCdev hR) hΦ
  have hpair := one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (I := I) (M := M) g W A
  have hshift :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ := by
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 3 U).symm
  change
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 W)).toFun A.toFun| ≤
      C * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ ^ 2
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A‖ := hpair
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ *
        (Capp * (Cdev * R) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖) :=
      mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = C * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) U‖ ^ 2 := by
      rw [hshift]
      dsimp only [C]
      ring

theorem top_pair_abs_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η : ℝ}, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∀ (T T' : SmoothCcTensor g 0 2)
            {δ : ℝ} (hδ_lt : δ < 1)
            (hδ : gFibreOpBound g
              (ccTensorBilinSymm (I := I) g T) δ)
            {δ' : ℝ} (hδ'_lt : δ' < 1)
            (hδ' : gFibreOpBound g
              (ccTensorBilinSymm (I := I) g T') δ')
            {R : ℝ}, 0 ≤ R → R ≤ ρ →
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
            ∀ U : SmoothCcTensor g 0 2,
            let Φ := rhsTopPathIntegral (I := I) (M := M) g T T'
                hδ_lt hδ hδ'_lt hδ' -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
                (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                  (iteratedCovGrad (I := I) g 0 2 2
                    (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  intro η hη
  obtain ⟨ρ₀, C, hρ₀, hC, hpair⟩ :=
    top_pair_h4_uniform (I := I) (M := M) hDim gBase hΛ
  let D : ℝ := 2 * (C + 1)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  let ρ : ℝ := min ρ₀ (η / D)
  have hρ : 0 < ρ := lt_min hρ₀ (div_pos hη hD)
  refine ⟨ρ, hρ, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  have hRρ₀ : R ≤ ρ₀ := hRρ.trans (min_le_left _ _)
  have hRsmall : R ≤ η / D := hRρ.trans (min_le_right _ _)
  have hDR : R * D ≤ η := (le_div_iff₀ hD).mp hRsmall
  have hCR : 2 * (C * R) ≤ η := by
    dsimp only [D] at hDR
    nlinarith
  have h := hpair g hEq hjet T T' hδ_lt hδ hδ'_lt hδ'
    hR hRρ₀ hT hT' U
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
          (operatorFieldApply (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g T T'
                hδ_lt hδ hδ'_lt hδ' -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
            (iteratedCovGrad (I := I) g 0 2 2
              (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun|
        ≤ 2 * (C * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (2 * (C * R)) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by ring
    _ ≤ η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCR (sq_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
