import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Forcing.SmoothIdentification
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Galerkin.CoordinateSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Remainder.ZeroOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def galerkinCoreRep (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    SmoothCcTensor g₀ 0 2 :=
  (min 1 (R / ‖galerkinLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ S c (((1 : ℕ) : ℝ) + 2))‖)) •
    finiteEigenCombo (I := I) (M := M) g₀ S c

theorem galerkinCoreRep_eq (g₀ : SmoothRiemannianMetric I M) (R : ℝ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (galerkinCoreRep (I := I) (M := M) g₀ R S c) =
      galerkinTameStateC (I := I) (M := M) g₀ 1 R S c := by
  rw [galerkinCoreRep, smoothCcToTensorHs_smul, ← finiteEigenComboHs_eq, galerkinTameStateC]

theorem galerkinRepHs_scale (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galerkinLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (ccTensor02Symm (I := I) (M := M) g₀
          (galerkinCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      θ * Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  let θ : ℝ := min 1 (R / ‖galerkinLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  refine (norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g₀ σ _).trans ?_
  have hrep : galerkinCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  rw [hnorm]

theorem galerkinRepHs_le (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (ccTensor02Symm (I := I) (M := M) g₀
          (galerkinCoreRep (I := I) (M := M) g₀ R F c))‖ ≤
      Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
  refine (norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g₀ σ _).trans ?_
  let θ : ℝ := min 1 (R / ‖galerkinLowView (I := I) (M := M) g₀ 1
    (finiteEigenComboHs (I := I) (M := M) g₀ F c (((1 : ℕ) : ℝ) + 2))‖)
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  have hθ1 : θ ≤ 1 := by
    dsimp only [θ]
    exact min_le_left _ _
  have hrep : galerkinCoreRep (I := I) (M := M) g₀ R F c =
      θ • finiteEigenCombo (I := I) (M := M) g₀ F c := rfl
  rw [hrep, smoothCcToTensorHs_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ0]
  have hnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ =
        Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    rw [← finiteEigenComboHs_eq]
    rw [← Real.sqrt_sq (norm_nonneg _),
      finiteEigenCombo_spectral_normSq (I := I) (M := M)]
    rfl
  calc
    θ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ ≤
        1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (finiteEigenCombo (I := I) (M := M) g₀ F c)‖ :=
      mul_le_mul_of_nonneg_right hθ1 (norm_nonneg _)
    _ = _ := by rw [one_mul, hnorm]

theorem galerkinCoreRep_ball (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galerkinCoreRep (I := I) (M := M) g₀ R S c))‖ ≤ R := by
  rw [galerkinCoreRep_eq]
  exact galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR S c

theorem galerkinState_mem_smoothCore (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    (⟨galerkinTameStateC (I := I) (M := M) g₀ 1 R S c,
        galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) ∈
      smoothCore (I := I) (M := M) g₀ R :=
  ⟨galerkinCoreRep (I := I) (M := M) g₀ R S c,
    galerkinCoreRep_eq (I := I) (M := M) g₀ R S c⟩

theorem galerkinRepFib (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (ccTensor02Symm (I := I) (M := M) g₀
          (galerkinCoreRep (I := I) (M := M) g₀ R S c))) δ :=
  hreal _ (symm_h2_of_state (I := I) (M := M) g₀
    (galerkinCoreRep (I := I) (M := M) g₀ R S c)
    (galerkinCoreRep_ball (I := I) (M := M) g₀ hR S c))

theorem zeroMetricPerturbation_fibre_bound (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 ≤ R)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
  refine hreal (0 : SmoothCcTensor g₀ 0 2) ?_
  rw [smoothCcToTensorHs_zero, norm_zero]
  exact hR

theorem galerkinN_eval (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal
        ⟨galerkinTameStateC (I := I) (M := M) g₀ 1 R S c,
          galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ =
      deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
        (ccTensor02Symm (I := I) (M := M) g₀
          (galerkinCoreRep (I := I) (M := M) g₀ R S c)) hδ
        (galerkinRepFib (I := I) (M := M) g₀ hR.le hreal S c) := by
  have hsub : (⟨galerkinTameStateC (I := I) (M := M) g₀ 1 R S c,
        galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) =
      ⟨smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
          (galerkinCoreRep (I := I) (M := M) g₀ R S c),
        galerkinCoreRep_ball (I := I) (M := M) g₀ hR.le S c⟩ :=
    Subtype.ext (galerkinCoreRep_eq (I := I) (M := M) g₀ R S c).symm
  rw [hsub]
  exact deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g₀ g₀ hR hδ hreal hcore
    (galerkinCoreRep (I := I) (M := M) g₀ R S c)
    (galerkinCoreRep_ball (I := I) (M := M) g₀ hR.le S c)

theorem galerkinTermId (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ hreal))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨galerkinTameStateC (I := I) (M := M) g₀ 1 R S c,
            galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ -
        deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
              (ccTensor02Symm (I := I) (M := M) g₀
                (galerkinCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galerkinRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)).secondOrderAction
            (I := I) (M := M)
            (ccTensor02Symm (I := I) (M := M) g₀
              (galerkinCoreRep (I := I) (M := M) g₀ R S c)) +
          (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
              (ccTensor02Symm (I := I) (M := M) g₀
                (galerkinCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galerkinRepFib (I := I) (M := M) g₀ hR.le hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)).firstOrderAction
            (I := I) (M := M)
            (ccTensor02Symm (I := I) (M := M) g₀
              (galerkinCoreRep (I := I) (M := M) g₀ R S c))) := by
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  set W := ccTensor02Symm (I := I) (M := M) g₀
    (galerkinCoreRep (I := I) (M := M) g₀ R S c) with hW
  set U : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨galerkinTameStateC (I := I) (M := M) g₀ 1 R S c,
      galerkinTameStateC_mem (I := I) (M := M) g₀ 1 hR.le S c⟩ with hU
  set Z : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ with hZ
  let P := galerkinRepFib (I := I) (M := M) g₀ hR.le hreal S c
  let P₀ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal
  let N := deTurckSmoothN (I := I) (M := M) g₀ g₀ 1 W hδ P
  let N₀ := deTurckSmoothN (I := I) (M := M) g₀ g₀ 1
    (0 : SmoothCcTensor g₀ 0 2) hδ P₀
  let Rm := deTurckSmoothRemainder (I := I) g₀ g₀ W hδ P
  let Rm₀ := deTurckSmoothRemainder (I := I) g₀ g₀
    (0 : SmoothCcTensor g₀ 0 2) hδ P₀
  set A :=
    (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ W hδ P P₀).secondOrderAction
        (I := I) (M := M) W +
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ W hδ P P₀).firstOrderAction
        (I := I) (M := M) W with hA
  have h₁ :
      deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal U -
          deTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hR hδ hreal Z =
        N - N₀ := by
    dsimp only [N, N₀, P, P₀, W]
    rw [hU, hZ]
    rw [galerkinN_eval (I := I) (M := M) g₀ hR hδ hreal hcore S c,
      deTurckRemainderOnLowerState_zero_eq_deTurckRHS (I := I) (M := M) g₀ g₀ hR hδ hreal hcore,
      ← deTurckSmoothN_zero (I := I) (M := M) g₀ g₀ 1 hδ
        (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR.le hreal)]
  have h₂ : N - N₀ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) (Rm - Rm₀) := by
    dsimp only [N, N₀, Rm, Rm₀, P, P₀]
    exact deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub (I := I) (M := M)
      g₀ g₀ 1 _ _ hδ _ hδ _
  have hsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g₀ W x u v = ccTensorBilin (I := I) g₀ W x v u := by
    rw [hW]
    exact smoothCcTensorBilinForm_ccTensor02Symm_symm
      (I := I) (M := M) g₀ (galerkinCoreRep (I := I) (M := M) g₀ R S c)
  have h₃ : Rm - Rm₀ = A := by
    rw [hA]
    dsimp only [Rm, Rm₀]
    exact (hsplit W hsymm hδ3 hδ0 P P₀).1
  exact h₁.trans (h₂.trans
    (congrArg (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)) h₃))

theorem galerkinTermCap (g₀ : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧
      ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
              (ccTensor02Symm (I := I) (M := M) g₀
                (galerkinCoreRep (I := I) (M := M) g₀ R S c)) hδ
              (galerkinRepFib (I := I) (M := M) g₀ hR hreal S c)
              (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).secondOrderCoefficient.toSection x) ≤
          Cδ ^ 2 := by
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  refine ⟨K * (δ / (1 - δ) ^ 2),
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro S c x
  exact (hsplit _
    (smoothCcTensorBilinForm_ccTensor02Symm_symm (I := I) (M := M)
      g₀ (galerkinCoreRep (I := I) (M := M) g₀ R S c))
    hδ3 hδ0 (galerkinRepFib (I := I) (M := M) g₀ hR hreal S c)
    (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀ hR hreal)).2 x

open scoped Classical in
theorem galerkinForceTerm (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galerkinTameForce (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal) S c i =
      if i ∈ S then
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
            ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩).coeff i +
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galerkinCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galerkinRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).secondOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galerkinCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)) +
              (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (galerkinCoreRep (I := I) (M := M) g₀
                      (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                  (galerkinRepFib (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                  (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                    (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                      (B1 := B1) (ρ := ρ) hP.le hreal))).firstOrderAction (I := I) (M := M)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galerkinCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)))).coeff i
      else 0 := by
  classical
  have harm := galerkinTermId (I := I) (M := M) g₀
    (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ hδ0 hδ3
    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal) hcore S c
  have hval : boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨galerkinTameStateC (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius Ctop B1 ρ P) S c,
          galerkinTameStateC_mem (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le S c⟩ =
      boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩ +
        smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galerkinCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                (galerkinRepFib (I := I) (M := M) g₀
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                  (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                  (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal))).secondOrderAction (I := I) (M := M)
              (ccTensor02Symm (I := I) (M := M) g₀
                (galerkinCoreRep (I := I) (M := M) g₀
                  (lowRegularityStateRadius Ctop B1 ρ P) S c)) +
            (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀
                (ccTensor02Symm (I := I) (M := M) g₀
                  (galerkinCoreRep (I := I) (M := M) g₀
                    (lowRegularityStateRadius Ctop B1 ρ P) S c)) hδ
                (galerkinRepFib (I := I) (M := M) g₀
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                  (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal) S c)
                (zeroMetricPerturbation_fibre_bound (I := I) (M := M) g₀
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
                  (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop)
                    (B1 := B1) (ρ := ρ) hP.le hreal))).firstOrderAction (I := I) (M := M)
              (ccTensor02Symm (I := I) (M := M) g₀
                (galerkinCoreRep (I := I) (M := M) g₀
                  (lowRegularityStateRadius Ctop B1 ρ P) S c))) :=
    sub_eq_iff_eq_add'.mp harm
  rw [galerkinTameForce_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, hval, TensorHs.add_coeff]
  · rw [if_neg hi, if_neg hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
