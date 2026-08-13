import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeEndpoint

open DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

section Scalar

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

abbrev duhamelKernelSqIntegral :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral

theorem two_lambda_mul_duhamelKernelSqIntegral (lam t : ℝ) :
    (2 * lam) * duhamelKernelSqIntegral lam t = 1 - Real.exp (-(2 * lam * t)) :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.two_lambda_mul_duhamelKernelSqIntegral
    lam t

theorem duhamelKernelSqIntegral_nonneg {lam t : ℝ} (ht : 0 ≤ t) :
    0 ≤ duhamelKernelSqIntegral lam t :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral_nonneg ht

theorem duhamelKernelSqIntegral_le_t {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    duhamelKernelSqIntegral lam t ≤ t :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.duhamelKernelSqIntegral_le_t hlam ht

theorem one_add_lambda_mul_duhamel_kernel_sq_integral_le {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    (1 + lam) * duhamelKernelSqIntegral lam t ≤ t + 1 / 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_duhamel_kernel_sq_integral_le
    hlam ht

variable {f : ℝ → ℝ}

theorem perModeConv_endpoint_sq_le (lam : ℝ) (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) :
    (perModeConv lam f t) ^ 2
      ≤ duhamelKernelSqIntegral lam t * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.perModeConv_endpoint_sq_le lam hf ht

theorem one_add_lambda_mul_perModeConv_endpoint_sq_le (lam : ℝ)
    (hlam : 0 ≤ lam) (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (1 + lam) * (perModeConv lam f t) ^ 2
      ≤ (t + 1 / 2) * ∫ s in (0 : ℝ)..t, f s ^ 2 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_perModeConv_endpoint_sq_le
    lam hlam hf ht

end Scalar

section Assembly

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_endpoint_value_weighted_summable
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (c + 1) *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hmass.mul_left (t + 1 / 2))
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (c + 1))
      (sq_nonneg _)
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hweight_split :
        tensorSobolevWeight (I := I) (M := M) i (c + 1) =
          tensorSobolevWeight (I := I) (M := M) i c * (1 + lam) := by
      have hbase_pos : (0 : ℝ) < 1 + lam :=
        lt_of_lt_of_le one_pos (by linarith)
      rw [tensorSobolevWeight, tensorSobolevWeight, hlam_def, Real.rpow_add hbase_pos,
        Real.rpow_one]
    have hwc_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i c
    have hgain := one_add_lambda_mul_perModeConv_endpoint_sq_le
      (f := φ i) lam hlam_nn (hφ i) ht
    calc tensorSobolevWeight (I := I) (M := M) i (c + 1) *
            (perModeConv lam (φ i) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i c *
            ((1 + lam) * (perModeConv lam (φ i) t) ^ 2) := by
          rw [hweight_split]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i c *
            ((t + 1 / 2) * ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) :=
          mul_le_mul_of_nonneg_left hgain hwc_nn
      _ = (t + 1 / 2) * (tensorSobolevWeight (I := I) (M := M) i c *
            ∫ s in (0 : ℝ)..t, (φ i s) ^ 2) := by ring

def duhamelValueHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    tensorHs (I := I) (M := M) g r s (c + 1) where
  coeff i := perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t
  weighted_summable :=
    duhamel_endpoint_value_weighted_summable (I := I) (M := M) c ht φ hφ hmass

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem duhamelValueHs_coeff {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_endpoint_value_summable_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {c : ℝ} (hc : 0 ≤ c) {t : ℝ}
    (ht : 0 ≤ t)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmass : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
  tensorHs.coeff_summable_sq_of_nonneg (I := I) (M := M) (by linarith : 0 ≤ c + 1)
    (duhamelValueHs (I := I) (M := M) c ht φ hφ hmass)

omit [NeZero (Module.finrank ℝ E)] in
theorem duhamel_into_all_tensorHs {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {t : ℝ} (ht : 0 ≤ t)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) :
    ∃ u : TensorL2 r s g,
      (∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ∧
      ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g r s σ,
          tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
              h_compact hσ v = u := by
  classical
  set bsis := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hbsis_def
  have hval_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) ^ 2) :=
    duhamel_endpoint_value_summable_sq (I := I) (M := M) (c := 0) le_rfl ht φ hφ
      (hsmooth 0 le_rfl)
  have hmemℓp : Memℓp (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t‖ ^
            (2 : ℝ≥0∞).toReal) =
        (fun i => (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (φ i) t) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]; exact hval_summable
  set u : TensorL2 r s g := bsis.repr.symm ⟨_, hmemℓp⟩ with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := by
    intro i
    rw [tensorL2Coeff, hu_def, hbsis_def,
      LinearIsometryEquiv.apply_symm_apply]
  refine ⟨u, hu_coeff, fun σ hσ => ?_⟩
  set c : ℝ := max (σ - 1) 0 with hc_def
  have hc_nn : 0 ≤ c := le_max_right _ _
  have hσ_le : σ ≤ c + 1 := by
    have : σ - 1 ≤ c := le_max_left _ _; linarith
  set vTop : tensorHs (I := I) (M := M) g r s (c + 1) :=
    duhamelValueHs (I := I) (M := M) (c := c) ht φ hφ (hsmooth c hc_nn) with hvTop_def
  have hv_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i σ * (vTop.coeff i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) vTop.weighted_summable
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
        (sq_nonneg _)
    · have hbase : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        one_le_one_add_lambda (I := I) (M := M) i
      have hwle : tensorSobolevWeight (I := I) (M := M) i σ ≤
          tensorSobolevWeight (I := I) (M := M) i (c + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase hσ_le
      exact mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
  set v : tensorHs (I := I) (M := M) g r s σ :=
    { coeff := vTop.coeff, weighted_summable := hv_summable } with hv_def
  refine ⟨v, ?_⟩
  refine bsis.repr.injective ?_
  ext i
  have hcoeff_lhs : (bsis.repr (tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s) h_compact hσ v)) i =
      tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ v) i := rfl
  have hcoeff_rhs : (bsis.repr u) i =
      tensorL2Coeff (I := I) (M := M) h_compact u i := rfl
  rw [hcoeff_lhs, hcoeff_rhs,
    tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ v i,
    hu_coeff i]
  rfl

theorem exists_smooth_tensor_representative_of_duhamel_smoothing
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ q in (0 : ℝ)..t, (φ i q) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      ∀ i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (T : TensorL2 r s g) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t := by
  obtain ⟨u, hu_coeff, hu_all⟩ :=
    duhamel_into_all_tensorHs (I := I) (M := M) ht
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      φ hφ hsmooth
  obtain ⟨T, hT⟩ := h_gate u hu_all
  refine ⟨T, fun i => ?_⟩
  rw [hT]
  exact hu_coeff i

end Assembly

end Spectral
end Analysis
end DifferentialGeometry

end
