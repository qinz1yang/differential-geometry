import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.MetricPerturbation.InverseH2
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.IteratedCovariantDerivative

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank2H4 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev rank2H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

noncomputable def secondCovariantDerivativeH4ToH2
    (g : SmoothRiemannianMetric I M) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank4H2 (I := I) (M := M) g := by
  let J : rank2H4 (I := I) (M := M) g →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + (2 : ℝ)) :=
    (TensorHs.castEquiv (I := I) (M := M)
      (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact (iterCovGradHs (I := I) (M := M) g 2 2 2).comp J

noncomputable def cometricDoubleTraceH2
    (g : SmoothRiemannianMetric I M) :
    rank4H2 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2)

theorem hessianH2_core
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 2) :
    secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  have hcast :
      (ContinuousLinearEquiv.toContinuousLinearMap
        (TensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U := by
    change
      TensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U
    ext i
    simp only [TensorHs.castEquiv_coeff, ccTensorToHs_coeff]
  rw [secondCovariantDerivativeH4ToH2, ContinuousLinearMap.comp_apply, hcast]
  exact iterCovGradHs_core (I := I) (M := M) g 2 2 2 U

theorem traceH2_core
    (g : SmoothRiemannianMetric I M) (V : SmoothCcTensor g 0 4) :
    cometricDoubleTraceH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) V) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceField (I := I) g 2) V) := by
  exact appHs_core (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2) V

noncomputable def lowRegularityPrincipalOperatorH2
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  (cometricDoubleTraceH2 (I := I) (M := M) g).comp
    ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp
      (secondCovariantDerivativeH4ToH2 (I := I) (M := M) g))

theorem lowRegularityPrincipalOperatorH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_norm_bound (I := I) (M := M) hDim g
  let A := cometricDoubleTraceH2 (I := I) (M := M) g
  let D := secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hInv := (hinv T hT).2
  calc
    ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T‖ ≤
        ‖A‖ *
          ‖(inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp D‖ := by
      simpa only [lowRegularityPrincipalOperatorH2, A, D] using
        (A.opNorm_comp_le
          ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).comp D))
    _ ≤ ‖A‖ *
          (‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

theorem lowRegularityPrincipalOperatorH2_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T U : metricH2 (I := I) (M := M) g,
        ‖T‖ ≤ ρ → ‖U‖ ≤ ρ →
          ‖lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T -
              lowRegularityPrincipalOperatorH2 (I := I) (M := M) g U‖ ≤
            C * ‖T - U‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricPerturbationCorrectionH2_lipschitz_bound (I := I) (M := M) hDim g
  let A := cometricDoubleTraceH2 (I := I) (M := M) g
  let D := secondCovariantDerivativeH4ToH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U hT hU
  have hInv := hinv T U hT hU
  have hdiff :
      lowRegularityPrincipalOperatorH2 (I := I) (M := M) g T -
          lowRegularityPrincipalOperatorH2 (I := I) (M := M) g U =
        A.comp
          ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
            inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).comp D) := by
    apply ContinuousLinearMap.ext
    intro V
    simp only [lowRegularityPrincipalOperatorH2, A, D, sub_apply,
      ContinuousLinearMap.comp_apply]
    rw [map_sub]
  rw [hdiff]
  calc
    _ ≤ ‖A‖ *
          ‖(inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
            inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).comp D‖ :=
      A.opNorm_comp_le _
    _ ≤ ‖A‖ *
          (‖inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
              inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g T -
          inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g U).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T - U‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T - U‖ := by
      dsimp only [C]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
