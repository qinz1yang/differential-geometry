import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.LowOrderCoefficientTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FirstOrderCoefficientTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Time
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Basic

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq covariantJetNormSq_sub_le
    exists_covariantJetNormSq_le_spectralSobolevNorm_sq iteratedCovGrad
    iteratedCovGrad_zero)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldComposition_add_left operatorFieldComposition_zero_eq_operatorFieldApply operatorFieldComposition_zero_left
    ccTensorToHs ccTensorToHs_add ccToHsLin ccToHsLin_apply ccToHsLin_dense
    deTurckSmoothRemainder iteratedCovGrad_smul)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem zero_fiber_bound
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

noncomputable def firstOrderCoreActionCoefficientsBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := 0
  firstOrderCoefficient := (lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient
  secondOrderCoefficient := 0

noncomputable def firstOrderCoreActionCoefficients
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g :=
  firstOrderCoreActionCoefficientsBackground (I := I) (M := M) g g hρ hδ0 hδ_le hreal T

noncomputable def combinedLowerScaleActionCoefficients
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient
  firstOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
    (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T).firstOrderCoefficient
  secondOrderCoefficient := (lowCoreActionCoefficientsBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T).secondOrderCoefficient

private theorem combinedLowerScaleActionCoefficients_C0
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient =
      (radialLowerScaleActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient := by
  rfl

private theorem combinedLowerScaleActionCoefficients_C1
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).firstOrderCoefficient =
      (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal T).firstOrderCoefficient := by
  rfl

private theorem combinedLowerScaleActionCoefficients_C2
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).secondOrderCoefficient =
      (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T).secondOrderCoefficient := by
  rfl

theorem combinedLowerScaleActionCoefficients_firstOrderActionSecondToFirstOrder
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T W : SmoothCcTensor g 0 2) :
    ((radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
        (firstOrderCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M))
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        ((combinedLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderAction (I := I) (M := M) W) := by
  let C := radialLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let O := firstOrderCoreActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change (C.firstOrderActionSecondToFirstOrder (I := I) (M := M) + O.firstOrderActionSecondToFirstOrder (I := I) (M := M))
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
    ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
      (F.firstOrderAction (I := I) (M := M) W)
  have hcore :
      C.firstOrderAction (I := I) (M := M) W + O.firstOrderAction (I := I) (M := M) W =
        F.firstOrderAction (I := I) (M := M) W := by
    simp only [C, O, F, combinedLowerScaleActionCoefficients, firstOrderCoreActionCoefficients, firstOrderCoreActionCoefficientsBackground, LowerScaleActionCoefficients.firstOrderAction,
      ← operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldComposition_zero_left, operatorFieldComposition_add_left,
      zero_add, add_assoc]
  rw [add_apply,
    firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g C W,
    firstOrderActionSecondToFirstOrder_apply_ccTensorToHs (I := I) (M := M) hDim g O W,
    ← ccTensorToHs_add, hcore]

private theorem combinedLowerScaleActionCoefficients_zero
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 0
          (lowRadial (I := I) (M := M) g ρ T)) =
      (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderAction (I := I) (M := M)
        (lowRadial (I := I) (M := M) g ρ T) := by
  simpa only [lowCoreActionCoefficientsBackground, iteratedCovGrad_zero] using
    radialLowerScaleActionCoefficients_apply_self (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T

private theorem combinedLowerScaleActionCoefficients_first
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.firstOrderAction (I := I) (M := M) S = F.firstOrderAction (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let C := radialLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change A.firstOrderAction (I := I) (M := M) S = F.firstOrderAction (I := I) (M := M) S
  have hzero := combinedLowerScaleActionCoefficients_zero (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  have hF0 : F.zeroOrderCoefficient = C.zeroOrderCoefficient :=
    combinedLowerScaleActionCoefficients_C0 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  have hF1 : F.firstOrderCoefficient = C.firstOrderCoefficient + A.firstOrderCoefficient :=
    combinedLowerScaleActionCoefficients_C1 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  simp only [iteratedCovGrad_zero, LowerScaleActionCoefficients.firstOrderAction] at hzero
  rw [LowerScaleActionCoefficients.firstOrderAction, LowerScaleActionCoefficients.firstOrderAction]
  rw [hF0, hF1]
  rw [operatorFieldApplication_add_left, hzero]
  abel

private theorem combinedLowerScaleActionCoefficients_second
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.secondOrderAction (I := I) (M := M) S = F.secondOrderAction (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change A.secondOrderAction (I := I) (M := M) S = F.secondOrderAction (I := I) (M := M) S
  have hF2 : F.secondOrderCoefficient = A.secondOrderCoefficient :=
    combinedLowerScaleActionCoefficients_C2 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  rw [LowerScaleActionCoefficients.secondOrderAction, LowerScaleActionCoefficients.secondOrderAction, hF2]

private theorem combinedLowerScaleActionCoefficients_action
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.secondOrderAction (I := I) (M := M) S + A.firstOrderAction (I := I) (M := M) S =
      F.secondOrderAction (I := I) (M := M) S + F.firstOrderAction (I := I) (M := M) S := by
  exact congrArg₂ (· + ·)
    (combinedLowerScaleActionCoefficients_second (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T)
    (combinedLowerScaleActionCoefficients_first (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T)

theorem deTurckSmoothRemainder_sub_eq_combined_actions
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let F := combinedLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g g S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fiber_bound (I := I) (M := M) g hδ0) =
      F.secondOrderAction (I := I) (M := M) S + F.firstOrderAction (I := I) (M := M) S := by
  exact (lowCoreBackground_split (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T).trans
      (combinedLowerScaleActionCoefficients_action (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T)

noncomputable def combinedLowerScaleActionCoefficientsBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient +
    ((lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient -
      (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient)
  firstOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
    (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient
  secondOrderCoefficient := (lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).secondOrderCoefficient

private theorem combinedLowerScaleActionCoefficientsBackground_C0
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient =
      (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient +
        ((lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient -
          (lowCoreActionCoefficientsBackground (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient) := by
  rfl

private theorem combinedLowerScaleActionCoefficientsBackground_C1
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient =
      (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient := by
  rfl

private theorem combinedLowerScaleActionCoefficientsBackground_C2
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).secondOrderCoefficient =
      (lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).secondOrderCoefficient := by
  rfl

theorem combinedLowerScaleActionCoefficientsBackground_self
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T =
      combinedLowerScaleActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T := by
  simp only [combinedLowerScaleActionCoefficientsBackground, combinedLowerScaleActionCoefficients, sub_self, add_zero]

private theorem combinedLowerScaleActionCoefficientsBackground_first
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.firstOrderAction (I := I) (M := M) S = F.firstOrderAction (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  let D := lowCoreActionCoefficientsBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let C := radialLowerScaleActionCoefficients (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  change A.firstOrderAction (I := I) (M := M) S = F.firstOrderAction (I := I) (M := M) S
  have hzero := combinedLowerScaleActionCoefficients_zero (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  have hF0 : F.zeroOrderCoefficient = C.zeroOrderCoefficient + (A.zeroOrderCoefficient - D.zeroOrderCoefficient) :=
    combinedLowerScaleActionCoefficientsBackground_C0 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  have hF1 : F.firstOrderCoefficient = C.firstOrderCoefficient + A.firstOrderCoefficient :=
    combinedLowerScaleActionCoefficientsBackground_C1 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  have hkey : operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient S =
      operatorFieldApply (I := I) (M := M) g 2 2 (A.zeroOrderCoefficient - D.zeroOrderCoefficient) S +
        operatorFieldApply (I := I) (M := M) g 2 2 D.zeroOrderCoefficient S := by
    rw [← operatorFieldApplication_add_left, sub_add_cancel]
  simp only [iteratedCovGrad_zero, LowerScaleActionCoefficients.firstOrderAction] at hzero
  rw [LowerScaleActionCoefficients.firstOrderAction, LowerScaleActionCoefficients.firstOrderAction]
  rw [hF0, hF1]
  rw [operatorFieldApplication_add_left, operatorFieldApplication_add_left, hkey, hzero]
  abel

private theorem combinedLowerScaleActionCoefficientsBackground_second
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.secondOrderAction (I := I) (M := M) S = F.secondOrderAction (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  change A.secondOrderAction (I := I) (M := M) S = F.secondOrderAction (I := I) (M := M) S
  have hF2 : F.secondOrderCoefficient = A.secondOrderCoefficient :=
    combinedLowerScaleActionCoefficientsBackground_C2 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  rw [LowerScaleActionCoefficients.secondOrderAction, LowerScaleActionCoefficients.secondOrderAction, hF2]

private theorem combinedLowerScaleActionCoefficientsBackground_action
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.secondOrderAction (I := I) (M := M) S + A.firstOrderAction (I := I) (M := M) S =
      F.secondOrderAction (I := I) (M := M) S + F.firstOrderAction (I := I) (M := M) S := by
  exact congrArg₂ (· + ·)
    (combinedLowerScaleActionCoefficientsBackground_second (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T)
    (combinedLowerScaleActionCoefficientsBackground_first (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T)

theorem deTurckSmoothRemainder_background_sub_eq_combined_actions
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let F := combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g gB
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fiber_bound (I := I) (M := M) g hδ0) =
      F.secondOrderAction (I := I) (M := M) S + F.firstOrderAction (I := I) (M := M) S := by
  exact (lowCoreBackground_split (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).trans
      (combinedLowerScaleActionCoefficientsBackground_action (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T)

noncomputable def backgroundDifferenceLowerScaleActionCoefficients
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient -
    (lowCoreActionCoefficientsBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient
  firstOrderCoefficient := 0
  secondOrderCoefficient := 0

private noncomputable def radialFirstOrderActionCoefficientsBackground
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).zeroOrderCoefficient +
    (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient
  firstOrderCoefficient := (radialLowerScaleActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
    (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient
  secondOrderCoefficient := 0

private theorem combinedBackgroundCoefficient_zero_decomposition
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient =
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient +
        (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).zeroOrderCoefficient := by
  simp only [combinedLowerScaleActionCoefficientsBackground, radialFirstOrderActionCoefficientsBackground, backgroundDifferenceLowerScaleActionCoefficients, firstOrderCoreActionCoefficientsBackground, add_zero]

private theorem combinedBackgroundCoefficient_one_decomposition
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient =
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient +
        (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).firstOrderCoefficient := by
  simp only [combinedLowerScaleActionCoefficientsBackground, radialFirstOrderActionCoefficientsBackground, backgroundDifferenceLowerScaleActionCoefficients, firstOrderCoreActionCoefficientsBackground, add_zero]

theorem combinedLowerScaleActionCoefficientsBackground_firstOrderActionThirdToSecondOrder_decomposition
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) =
      ((radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) +
        (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M)) +
      (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M) := by
  rw [firstOrderActionThirdToSecondOrder_add (I := I) (M := M) hDim g
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedBackgroundCoefficient_zero_decomposition (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedBackgroundCoefficient_one_decomposition (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T),
    firstOrderActionThirdToSecondOrder_add (I := I) (M := M) hDim g
      (radialLowerScaleActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T)
      (firstOrderCoreActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      rfl rfl]

theorem combinedLowerScaleActionCoefficientsBackground_firstOrderActionSecondToFirstOrder_decomposition
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) =
      ((radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
        (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M)) +
      (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
  rw [firstOrderActionSecondToFirstOrder_add (I := I) (M := M) hDim g
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedLowerScaleActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedBackgroundCoefficient_zero_decomposition (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (combinedBackgroundCoefficient_one_decomposition (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T),
    firstOrderActionSecondToFirstOrder_add (I := I) (M := M) hDim g
      (radialLowerScaleActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T)
      (firstOrderCoreActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (radialFirstOrderActionCoefficientsBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      rfl rfl]

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

theorem exists_background_first_order_continuous_operator_extensions
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ S : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder
                    (I := I) (M := M) +
                (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
                  g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder
                    (I := I) (M := M)) ∧
            (∀ S : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
                    (I := I) (M := M) +
                (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
                  g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
                    (I := I) (M := M)) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) := by
  obtain ⟨ρc, hρc, hc⟩ := exists_radialLowerScaleActionCoefficients_continuous_operator_extensions (I := I) (M := M) hDim g
  obtain ⟨ρo, hρo, ho⟩ := exists_backgroundFirstOrderCoefficient_continuous_operator_extensions (I := I) (M := M) hDim g gB
  let ρ0 : ℝ := min ρc ρo
  have hρ0 : 0 < ρ0 := lt_min hρc hρo
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  have hρc' : ρ ≤ ρc := hρρ0.trans (min_le_left _ _)
  have hρo' : ρ ≤ ρo := hρρ0.trans (min_le_right _ _)
  obtain ⟨Zc, Lc, hZc, hLc, FcHi, FcLo, hFcHi, hFcLo,
      hcHiCore, hcLoCore, hcHiBd, hcLoBd, hcComm⟩ :=
    hc hρ hρc' hδ0 hδ_le hreal
  obtain ⟨Zo, Lo, hZo, hLo, FoHi, FoLo, hFoHi, hFoLo,
      hoHiCore, hoLoCore, hoHiBd, hoLoBd, hoComm⟩ :=
    ho hρ hρo' hδ0 hδ_le hreal
  let Z : ℝ := Zc + Zo
  let L : ℝ := Lc + Lo
  let FHi : metricThirdOrderSobolev (I := I) (M := M) g →
      (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun x => FcHi x + FoHi x
  let FLo : metricThirdOrderSobolev (I := I) (M := M) g →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun x => FcLo x + FoLo x
  have hZ : 0 ≤ Z := add_nonneg hZc hZo
  have hL : 0 ≤ L := add_nonneg hLc hLo
  have hFHi : Continuous FHi := hFcHi.add hFoHi
  have hFLo : Continuous FLo := hFcLo.add hFoLo
  have hFHiBd : ∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
      ‖FHi x‖ ≤ Z + L * ‖x‖ := by
    intro x
    calc
      ‖FHi x‖ ≤ ‖FcHi x‖ + ‖FoHi x‖ := by
        simpa only [FHi] using norm_add_le (FcHi x) (FoHi x)
      _ ≤ (Zc + Lc * ‖x‖) + (Zo + Lo * ‖x‖) :=
        add_le_add (hcHiBd x) (hoHiBd x)
      _ = Z + L * ‖x‖ := by
        simp only [Z, L]
        ring
  have hFLoBd : ∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
      ‖FLo x‖ ≤ Z + L * ‖x‖ := by
    intro x
    calc
      ‖FLo x‖ ≤ ‖FcLo x‖ + ‖FoLo x‖ := by
        simpa only [FLo] using norm_add_le (FcLo x) (FoLo x)
      _ ≤ (Zc + Lc * ‖x‖) + (Zo + Lo * ‖x‖) :=
        add_le_add (hcLoBd x) (hoLoBd x)
      _ = Z + L * ‖x‖ := by
        simp only [Z, L]
        ring
  have hHiCore : ∀ S : SmoothCcTensor g 0 2,
      FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder (I := I) (M := M) +
        (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder (I := I) (M := M) := by
    intro S
    rw [show FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        FcHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
          FoHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) by rfl,
      hcHiCore S, hoHiCore S]
    rfl
  have hLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
        (firstOrderCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
    intro S
    rw [show FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        FcLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
          FoLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) by rfl,
      hcLoCore S, hoLoCore S]
    rfl
  have hcomm : ∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have h1 := DFunLike.congr_fun (hcComm x) v
    have h2 := DFunLike.congr_fun (hoComm x) v
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    have hv : FHi x v = FcHi x v + FoHi x v := rfl
    have hw : FLo x (incl32 (I := I) (M := M) g v) =
        FcLo x (incl32 (I := I) (M := M) g v) +
          FoLo x (incl32 (I := I) (M := M) g v) := rfl
    simp only [ContinuousLinearMap.comp_apply, hv, hw, map_add, h1, h2]
  exact ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo,
    hHiCore, hLoCore, hFHiBd, hFLoBd, hcomm⟩

theorem exists_first_order_continuous_operator_extensions
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricThirdOrderSobolev (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ S : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder
                    (I := I) (M := M) +
                (firstOrderCoreActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder
                    (I := I) (M := M)) ∧
            (∀ S : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (radialLowerScaleActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
                    (I := I) (M := M) +
                (firstOrderCoreActionCoefficients (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
                    (I := I) (M := M)) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) :=
  exists_background_first_order_continuous_operator_extensions (I := I) (M := M) hDim g g

def HasBackgroundDifferenceContinuousOperatorExtensions (g gB : SmoothRiemannianMetric I M) : Prop :=
  ∃ ρ0 : ℝ, 0 < ρ0 ∧
    ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
      (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
      (hreal : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ),
    ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
      ∃ GHi : metricThirdOrderSobolev (I := I) (M := M) g →
            (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
              metricH2 (I := I) (M := M) g),
        ∃ GLo : metricThirdOrderSobolev (I := I) (M := M) g →
            (metricH2 (I := I) (M := M) g →L[ℝ]
              metricH1 (I := I) (M := M) g),
          Continuous GHi ∧ Continuous GLo ∧
          (∀ S : SmoothCcTensor g 0 2,
            GHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
              (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionThirdToSecondOrder
                  (I := I) (M := M)) ∧
          (∀ S : SmoothCcTensor g 0 2,
            GLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
              (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal S).firstOrderActionSecondToFirstOrder
                  (I := I) (M := M)) ∧
          (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
            ‖GHi x‖ ≤ Z + L * ‖x‖) ∧
          (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
            ‖GLo x‖ ≤ Z + L * ‖x‖) ∧
          (∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
            (incl12 (I := I) (M := M) g).comp (GHi x) =
              (GLo x).comp (incl32 (I := I) (M := M) g))

private noncomputable def zeroBundle
    (g : SmoothRiemannianMetric I M) : LowerScaleActionCoefficients g where
  zeroOrderCoefficient := 0
  firstOrderCoefficient := 0
  secondOrderCoefficient := 0

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem zeroBundle_a1
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    (zeroBundle (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W = 0 := by
  simp only [zeroBundle, LowerScaleActionCoefficients.firstOrderAction, ← operatorFieldComposition_zero_eq_operatorFieldApply,
    operatorFieldComposition_zero_left, zero_add]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iterZ
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j
        (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_smul (I := I) (M := M) g r s j
    (0 : ℝ) (0 : SmoothCcTensor g r s)
  simpa only [zero_smul] using h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem lowJetZ
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    covariantJetNormSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  simp only [covariantJetNormSq, iterZ (I := I) (M := M), norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]

private theorem zeroBundle_pair
    (g : SmoothRiemannianMetric I M) :
    (zeroBundle (I := I) (M := M) g).firstOrderActionThirdToSecondOrder (I := I) (M := M) = 0 ∧
      (zeroBundle (I := I) (M := M) g).firstOrderActionSecondToFirstOrder (I := I) (M := M) = 0 := by
  obtain ⟨C, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          ((zeroBundle (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W) ≤
        (0 : ℝ) * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    rw [zeroBundle_a1 (I := I) (M := M),
      lowJetZ (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          ((zeroBundle (I := I) (M := M) g).firstOrderAction (I := I) (M := M) W) ≤
        (0 : ℝ) * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    rw [zeroBundle_a1 (I := I) (M := M),
      lowJetZ (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  obtain ⟨hHiNorm, hLoNorm, _⟩ := hpair
    (zeroBundle (I := I) (M := M) g) 0 le_rfl hHi hLo
  constructor
  · refine (ContinuousLinearMap.opNorm_zero_iff _).mp
      (le_antisymm ?_ (norm_nonneg _))
    simpa only [Real.sqrt_zero, mul_zero] using hHiNorm
  · refine (ContinuousLinearMap.opNorm_zero_iff _).mp
      (le_antisymm ?_ (norm_nonneg _))
    simpa only [Real.sqrt_zero, mul_zero] using hLoNorm

private theorem c0bg_aff
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∀ T : SmoothCcTensor g 0 2,
          ‖(backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
            ‖(backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  obtain ⟨B0, B1, hB0, hB1, htame⟩ :=
    exists_lowerScaleZeroCoefficient_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g gB
  obtain ⟨C2, hC2, hjet2⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C3, hC3, hjet3⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  obtain ⟨Ca, hCa, hact⟩ := exists_firstOrderAction_spectralSobolev_difference_bounds (I := I) (M := M) hDim g
  refine ⟨1, one_pos, ?_⟩
  intro ρ δ hρ _ hδ0 hδ_le hreal
  let R2 : ℝ := C2 * ρ
  let Z : ℝ := Ca * B0 R2
  let L : ℝ := Ca * B1 R2 * C3
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hZ : 0 ≤ Z := mul_nonneg hCa (hB0 R2 hR2)
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg hCa (hB1 R2 hR2)) hC3
  refine ⟨Z, L, hZ, hL, ?_⟩
  intro T
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let A : LowerScaleActionCoefficients g := backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal T
  let A3 : ℝ := C3 *
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  let Q : ℝ := B0 R2 + B1 R2 * A3
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 (norm_nonneg _)
  have hQ : 0 ≤ Q := add_nonneg (hB0 R2 hR2)
    (mul_nonneg (hB1 R2 hR2) hA3)
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fiber_bound (I := I) (M := M) g hδ0
  have hS2 : covariantJetNormSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hS3n :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad
  have hS3 : covariantJetNormSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hS3n hC3) 2
  have hraw := htame S hδ_le hδ0 hSδ hZδ R2 A3 hR2 hA3 hS2 hS3
  have hcoeffAct :
      covariantJetNormSq (I := I) (M := M) g 2
          (A.zeroOrderCoefficient - (zeroBundle (I := I) (M := M) g).zeroOrderCoefficient) +
        covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderCoefficient - (zeroBundle (I := I) (M := M) g).firstOrderCoefficient) ≤ Q ^ 2 := by
    have hC1 :
        covariantJetNormSq (I := I) (M := M) g 2
            (A.firstOrderCoefficient - (zeroBundle (I := I) (M := M) g).firstOrderCoefficient) = 0 := by
      simp only [A, backgroundDifferenceLowerScaleActionCoefficients, zeroBundle, sub_zero]
      exact lowJetZ (I := I) (M := M) g 3 2 2
    have hcoreB :
        lowCoreActionCoefficientsBackground (I := I) (M := M)
            g gB hρ.le hδ0 hδ_le hreal T =
          lowerScaleActionCoefficients (I := I) (M := M) g gB S
            (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ := by
      unfold lowCoreActionCoefficientsBackground
      dsimp only [S]
    have hcoreSelf :
        lowCoreActionCoefficientsBackground (I := I) (M := M)
            g g hρ.le hδ0 hδ_le hreal T =
          lowerScaleActionCoefficients (I := I) (M := M) g g S
            (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ := by
      unfold lowCoreActionCoefficientsBackground
      dsimp only [S]
    have hA0 :
        A.zeroOrderCoefficient -
            (zeroBundle (I := I) (M := M) g).zeroOrderCoefficient =
          (lowerScaleActionCoefficients (I := I) (M := M) g gB S
              (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient -
            (lowerScaleActionCoefficients (I := I) (M := M) g g S
              (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient := by
      change
        ((lowCoreActionCoefficientsBackground (I := I) (M := M)
              g gB hρ.le hδ0 hδ_le hreal T).zeroOrderCoefficient -
            (lowCoreActionCoefficientsBackground (I := I) (M := M)
              g g hρ.le hδ0 hδ_le hreal T).zeroOrderCoefficient) - 0 = _
      rw [sub_zero, hcoreB, hcoreSelf]
    rw [hC1, add_zero]
    rw [hA0]
    exact hraw
  have hop := hact A (zeroBundle (I := I) (M := M) g) Q hQ hcoeffAct
  obtain ⟨hzHi, hzLo⟩ := zeroBundle_pair (I := I) (M := M) g
  constructor
  · calc
      ‖A.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzHi, sub_zero] using hop.1
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring
  · calc
      ‖A.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzLo, sub_zero] using hop.2
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring

private theorem c0bg_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (r : ℝ),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        let AT := backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T
        let AU := backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal U
        ‖AT.firstOrderActionThirdToSecondOrder (I := I) (M := M) - AU.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ∧
          ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρb, Bsb, B0b, B1b, hρb, hBsb, hB0b, hB1b, hb⟩ :=
    zeroOrderBackgroundCoefficient_pairing_h2_bound (I := I) (M := M) hDim g gB
  obtain ⟨ρs, Bss, B0s, B1s, hρs, hBss, hB0s, hB1s, hs⟩ :=
    zeroOrderBackgroundCoefficient_pairing_h2_bound (I := I) (M := M) hDim g g
  obtain ⟨C2, hC2, hjet2⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 2
  obtain ⟨C3, hC3, hjet3⟩ := exists_covariantJetNormSq_le_spectralSobolevNorm_sq (I := I) (M := M) g 2 3
  obtain ⟨Ca, hCa, hact⟩ := exists_firstOrderAction_spectralSobolev_difference_bounds (I := I) (M := M) hDim g
  refine ⟨min ρb ρs, lt_min hρb hρs, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal r
  have hρb' : ρ ≤ ρb := hρρ0.trans (min_le_left _ _)
  have hρs' : ρ ≤ ρs := hρρ0.trans (min_le_right _ _)
  let r0 : ℝ := max r 0
  let R2 : ℝ := C2 * ρ
  let A3 : ℝ := C3 * r0
  let Lr : ℝ := 1 + (1 / ρ) * r0
  let W : ℝ := C3 * Lr + C2 + 1
  let Pb : ℝ := Bsb R2 * (1 + A3 ^ 2) * W
  let Qb : ℝ := B0b R2 * (C3 * Lr) + B1b R2 * C2 +
    B1b R2 * A3 * C2 + B1b R2 + B1b R2 * A3
  let Ps : ℝ := Bss R2 * (1 + A3 ^ 2) * W
  let Qs : ℝ := B0s R2 * (C3 * Lr) + B1s R2 * C2 +
    B1s R2 * A3 * C2 + B1s R2 + B1s R2 * A3
  let Ebg : ℝ := 4 * (Pb ^ 2 + Qb ^ 2 + Ps ^ 2 + Qs ^ 2)
  let Kc : ℝ := Real.sqrt Ebg
  have hr0 : 0 ≤ r0 := le_max_right r 0
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 hr0
  have hLr : 0 ≤ Lr := by
    simp only [Lr]
    positivity
  have hEbg : 0 ≤ Ebg := by
    simp only [Ebg]
    positivity
  have hKc : 0 ≤ Kc := Real.sqrt_nonneg _
  have hKcsq : Kc ^ 2 = Ebg := Real.sq_sqrt hEbg
  refine ⟨Ca * Kc, mul_nonneg hCa hKc, ?_⟩
  intro T U hTr hUr
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D2 : ℝ := C2 * D
  let D3 : ℝ := C3 * Lr * D
  let S : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ T
  let V : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ U
  have hD : 0 ≤ D := norm_nonneg _
  have hD2 : 0 ≤ D2 := mul_nonneg hC2 hD
  have hD3 : 0 ≤ D3 := mul_nonneg (mul_nonneg hC3 hLr) hD
  have hTr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r0 :=
    hTr.trans (le_max_left r 0)
  have hUr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 :=
    hUr.trans (le_max_left r 0)
  have hSρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hVρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le U
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hVδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g V) δ := hreal V hVρ
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fiber_bound (I := I) (M := M) g hδ0
  have hS2 : covariantJetNormSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hV2 : covariantJetNormSq (I := I) (M := M) g 2 V ≤ R2 ^ 2 := by
    refine (hjet2 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVρ hC2) 2
  have hStop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad.trans hTr0
  have hVtop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simpa only [V, ccToHsLin_apply] using hrad.trans hUr0
  have hS3 : covariantJetNormSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hStop hC3) 2
  have hV3 : covariantJetNormSq (I := I) (M := M) g 3 V ≤ A3 ^ 2 := by
    refine (hjet3 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVtop hC3) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ 3 by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, RicciDeTurckPairing.tensorHsInclusion_ccTensorToHs_two_three (I := I) (M := M) g T,
      RicciDeTurckPairing.tensorHsInclusion_ccTensorToHs_two_three (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hSV2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤ D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V]
    exact (lowRadial_lip (I := I) (M := M) g hρ.le T U).trans hincl
  have hSV2j : covariantJetNormSq (I := I) (M := M) g 2 (S - V) ≤ D2 ^ 2 := by
    refine (hjet2 (S - V)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV2 hC2) 2
  have hmax :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 := by
    simpa only [ccToHsLin_apply] using max_le hTr0 hUr0
  have hprod :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ r0 * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr0
  have hSV3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V)‖ ≤
      Lr * D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) S V]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod
      ((one_div_pos.mpr hρ).le)
    have hscaled' :
        (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r0 * D) := by
      calc
        _ = (1 / ρ) *
            (max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r0 * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        D + (1 / ρ) * (r0 * D) := by
          change D + _ ≤ D + _
          exact add_le_add_right hscaled' D
      _ = Lr * D := by
        simp only [Lr]
        ring
  have hSV3j : covariantJetNormSq (I := I) (M := M) g 3 (S - V) ≤ D3 ^ 2 := by
    refine (hjet3 (S - V)).trans ?_
    have hSV3' :
        ‖ccTensorToHs (I := I) (M := M) g 2 ((3 : ℕ) : ℝ) (S - V)‖ ≤
          Lr * D := by
      simpa only [Nat.cast_ofNat] using hSV3
    simpa only [D3, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV3' hC3) 2
  have hbg := hb S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    R2 A3 D2 D3 D hR2 hA3 hD2 hD3 hD
    hS2 hV2 hS3 hV3 hSV2j hSV3j
    (hSρ.trans hρb') (hVρ.trans hρb') hSV2
  have hself := hs S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    R2 A3 D2 D3 D hR2 hA3 hD2 hD3 hD
    hS2 hV2 hS3 hV3 hSV2j hSV3j
    (hSρ.trans hρs') (hVρ.trans hρs') hSV2
  have hbg' : covariantJetNormSq (I := I) (M := M) g 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g gB V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).zeroOrderCoefficient) ≤
      2 * (Pb ^ 2 + Qb ^ 2) * D ^ 2 := by
    refine hbg.trans (le_of_eq ?_)
    simp only [Pb, Qb, D2, D3, W]
    ring
  have hself' : covariantJetNormSq (I := I) (M := M) g 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g g S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).zeroOrderCoefficient) ≤
      2 * (Ps ^ 2 + Qs ^ 2) * D ^ 2 := by
    refine hself.trans (le_of_eq ?_)
    simp only [Ps, Qs, D2, D3, W]
    ring
  let AT : LowerScaleActionCoefficients g := backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal T
  let AU : LowerScaleActionCoefficients g := backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal U
  have hsplit : AT.zeroOrderCoefficient - AU.zeroOrderCoefficient =
      ((lowerScaleActionCoefficients (I := I) (M := M) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g gB V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).zeroOrderCoefficient) -
      ((lowerScaleActionCoefficients (I := I) (M := M) g g S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).zeroOrderCoefficient) := by
    simp only [AT, AU, backgroundDifferenceLowerScaleActionCoefficients, lowCoreActionCoefficientsBackground, S, V]
    abel
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 (AT.zeroOrderCoefficient - AU.zeroOrderCoefficient) +
        covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) ≤ (Kc * D) ^ 2 := by
    have hC1 : covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) = 0 := by
      simp only [AT, AU, backgroundDifferenceLowerScaleActionCoefficients, sub_self]
      exact lowJetZ (I := I) (M := M) g 3 2 2
    rw [hC1, add_zero, hsplit]
    refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 _ _).trans ?_
    have hsum := add_le_add hbg' hself'
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
          covariantJetNormSq (I := I) (M := M) g 2 _) ≤
          2 * (2 * (Pb ^ 2 + Qb ^ 2) * D ^ 2 +
            2 * (Ps ^ 2 + Qs ^ 2) * D ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = Ebg * D ^ 2 := by
        simp only [Ebg]
        ring
      _ = (Kc * D) ^ 2 := by
        rw [show (Kc * D) ^ 2 = Kc ^ 2 * D ^ 2 by ring, hKcsq]
  have hout := hact AT AU (Kc * D) (mul_nonneg hKc hD) hcoeff
  refine ⟨?_, ?_⟩
  · calc
      ‖AT.firstOrderActionThirdToSecondOrder (I := I) (M := M) - AU.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
          Ca * (Kc * D) := hout.1
      _ = Ca * Kc * D := by ring
  · calc
      ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          Ca * (Kc * D) := hout.2
      _ = Ca * Kc * D := by ring

theorem hasBackgroundDifferenceContinuousOperatorExtensions
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    HasBackgroundDifferenceContinuousOperatorExtensions (I := I) (M := M) g gB := by
  obtain ⟨ρp, hρp, hpair⟩ := c0bg_pair (I := I) (M := M) hDim g gB
  obtain ⟨ρa, hρa, haff⟩ := c0bg_aff (I := I) (M := M) hDim g gB
  let ρ0 : ℝ := min ρp ρa
  have hρ0 : 0 < ρ0 := lt_min hρp hρa
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  have hρp' : ρ ≤ ρp := hρρ0.trans (min_le_left _ _)
  have hρa' : ρ ≤ ρa := hρρ0.trans (min_le_right _ _)
  obtain ⟨Z, L, hZ, hL, hbd⟩ :=
    haff hρ hρa' hδ0 hδ_le hreal
  let fHi : SmoothCcTensor g 0 2 →
      (metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun T =>
    (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder (I := I) (M := M)
  let fLo : SmoothCcTensor g 0 2 →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun T =>
    (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder (I := I) (M := M)
  have hpairHi : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fHi T - fHi U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fHi] using (hK T U hT hU).1
  have hpairLo : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fLo T - fLo U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fLo] using (hK T U hT hU).2
  have hbdHi : ∀ T : SmoothCcTensor g 0 2,
      ‖fHi T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fHi] using (hbd T).1
  have hbdLo : ∀ T : SmoothCcTensor g 0 2,
      ‖fLo T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fLo] using (hbd T).2
  have hΦ : Continuous (fun x : ℝ => Z + L * x) := by
    fun_prop
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  obtain ⟨GHi, hGHi, hGHiCore, hGHiBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fHi hΦ hpairHi hbdHi
  obtain ⟨GLo, hGLo, hGLoCore, hGLoBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fLo hΦ hpairLo hbdLo
  have hleft : Continuous (fun x : metricThirdOrderSobolev (I := I) (M := M) g =>
      (incl12 (I := I) (M := M) g).comp (GHi x)) :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (continuous_const.prodMk hGHi)
  have hright : Continuous (fun x : metricThirdOrderSobolev (I := I) (M := M) g =>
      (GLo x).comp (incl32 (I := I) (M := M) g)) :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (hGLo.prodMk continuous_const)
  have hcomm : ∀ x : metricThirdOrderSobolev (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (GHi x) =
        (GLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    refine hdense.induction_on x (isClosed_eq hleft hright) ?_
    intro T
    rw [hGHiCore T, hGLoCore T]
    simpa only [incl12, incl32] using
      first_order_action_sobolev_extensions_commute (I := I) (M := M) hDim g
        (backgroundDifferenceLowerScaleActionCoefficients (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T)
  exact ⟨Z, L, hZ, hL, GHi, GLo, hGHi, hGLo,
    hGHiCore, hGLoCore, hGHiBd, hGLoBd, hcomm⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
