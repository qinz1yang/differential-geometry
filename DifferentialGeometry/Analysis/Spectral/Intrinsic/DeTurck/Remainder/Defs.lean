import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.Reverse.HebeyToHilbertSobolev
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.PartitionOfUnityNormComparison
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def deTurckSmoothRemainder (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }
  - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

def smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    TensorHs (I := I) (M := M) g₀ 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem smoothCcToTensorHs_coeff (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

@[simp] theorem smoothCcToTensorHs_zero (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  refine DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs.ext ?_
  funext i
  rw [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _]
  rw [tensorL2Coeff_eq_inner, inner_zero_right]
  rfl

theorem norm_smoothCcToTensorHs_zero_le (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
  rw [smoothCcToTensorHs_zero, norm_zero]
  exact hR

theorem finiteEigenComboHs_eq (g₀ : SmoothRiemannianMetric I M)
    (F : Finset (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2))
    (c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ) (σ : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ F c σ =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ F c) := by
  refine TensorHs.ext ?_
  funext i
  rw [finiteEigenComboHs_coeff_eq, smoothCcToTensorHs_coeff,
    ← SmoothCcTensor.toL2_apply]

def deTurckTermFibreConst (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) ^ 3)

lemma de_turck_term_fibre_const_nonneg (n : ℕ) : 0 ≤ deTurckTermFibreConst n :=
  Real.sqrt_nonneg _

lemma one_le_de_turck_term_fibre_const {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ deTurckTermFibreConst n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := (one_pow 3).symm
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ zero_le_one hn' 3
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt ((n : ℝ) ^ 3) := Real.sqrt_le_sqrt h1

lemma sq_de_turck_term_fibre_const (n : ℕ) :
    deTurckTermFibreConst n ^ 2 = (n : ℝ) ^ 3 :=
  Real.sq_sqrt (by positivity)

def deTurckContractionThreshold (n : ℕ) : ℝ :=
  1 / (1 + 2 * deTurckTermFibreConst n)

lemma de_turck_contraction_threshold_pos (n : ℕ) :
    0 < deTurckContractionThreshold n := by
  have h := de_turck_term_fibre_const_nonneg n
  unfold deTurckContractionThreshold
  positivity

lemma de_turck_contraction_threshold_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckContractionThreshold n ≤ 1 / 3 := by
  have h1 := one_le_de_turck_term_fibre_const hn
  unfold deTurckContractionThreshold
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 3)]
  linarith

lemma de_turck_contraction_threshold_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckContractionThreshold n < 1 :=
  lt_of_le_of_lt (de_turck_contraction_threshold_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma de_turck_contraction_threshold_le_third_of_ne_zero (n : ℕ) [NeZero n] :
    deTurckContractionThreshold n ≤ 1 / 3 :=
  de_turck_contraction_threshold_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma de_turck_contraction_threshold_lt_one_of_ne_zero (n : ℕ) [NeZero n] :
    deTurckContractionThreshold n < 1 :=
  de_turck_contraction_threshold_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

def deTurckRemainderContractionThreshold (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckTermFibreConst n + 32 * deTurckTermFibreConst n ^ 3))

lemma de_turck_remainder_contraction_threshold_pos (n : ℕ) :
    0 < deTurckRemainderContractionThreshold n := by
  unfold deTurckRemainderContractionThreshold
  have hf : 0 ≤ deTurckTermFibreConst n := de_turck_term_fibre_const_nonneg n
  have hf3 : 0 ≤ deTurckTermFibreConst n ^ 3 := by positivity
  exact one_div_pos.mpr (by linarith)

lemma de_turck_remainder_contraction_threshold_le_contraction_threshold {n : ℕ} (hn : 1 ≤ n) :
    deTurckRemainderContractionThreshold n ≤ deTurckContractionThreshold n := by
  have hC := one_le_de_turck_term_fibre_const hn
  unfold deTurckRemainderContractionThreshold deTurckContractionThreshold
  have hC3 : 0 ≤ deTurckTermFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma de_turck_remainder_contraction_threshold_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckRemainderContractionThreshold n ≤ 1 / 3 :=
  le_trans (de_turck_remainder_contraction_threshold_le_contraction_threshold hn)
    (de_turck_contraction_threshold_le_third hn)

lemma de_turck_remainder_contraction_threshold_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckRemainderContractionThreshold n < 1 :=
  lt_of_le_of_lt (de_turck_remainder_contraction_threshold_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma de_turck_remainder_contraction_threshold_le_third_of_ne_zero (n : ℕ) [NeZero n] :
    deTurckRemainderContractionThreshold n ≤ 1 / 3 :=
  de_turck_remainder_contraction_threshold_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma de_turck_remainder_contraction_threshold_lt_one_of_ne_zero (n : ℕ) [NeZero n] :
    deTurckRemainderContractionThreshold n < 1 :=
  de_turck_remainder_contraction_threshold_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma de_turck_term_fibre_const_mul_div_le_half {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckContractionThreshold n) :
    deTurckTermFibreConst n * (δ / (1 - δ)) ≤ 1 / 2 := by
  have hC := one_le_de_turck_term_fibre_const hn
  set C := deTurckTermFibreConst n with hC_def
  have hden : (0 : ℝ) < 1 + 2 * C := by linarith
  have hthr_lt : deTurckContractionThreshold n < 1 :=
    de_turck_contraction_threshold_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have : C * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hratio_np
    linarith
  · have hδ_mul : δ * (1 + 2 * C) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * C) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * C) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * C)]
      nlinarith
    calc C * (δ / (1 - δ)) ≤ C * (1 / (2 * C)) :=
          mul_le_mul_of_nonneg_left hratio (by linarith)
      _ = 1 / 2 := by field_simp

end DifferentialGeometry.Analysis.Spectral

end
