import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic


noncomputable section

namespace MeasureTheory

open Filter Set
open scoped Topology

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} [IsFiniteMeasure μ]

theorem integrable_mul_and_abs_integral_le_of_ae_abs_le
    {f eta : T → ℝ} (hf : Integrable f μ) (heta : AEStronglyMeasurable eta μ)
    {C K : ℝ}
    (hfbound : ∀ᵐ t ∂μ, |f t| ≤ C) (hetabound : ∀ᵐ t ∂μ, |eta t| ≤ K) :
    Integrable (fun t => eta t * f t) μ ∧
      |∫ t, eta t * f t ∂μ| ≤ K * C * μ.real univ := by
  have hetaNorm : ∀ᵐ t ∂μ, ‖eta t‖ ≤ K := by
    simpa only [Real.norm_eq_abs] using hetabound
  have hnorm : ∀ᵐ t ∂μ, ‖eta t * f t‖ ≤ K * C := by
    filter_upwards [hfbound, hetabound] with t ht hetaT
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hetaT ht (abs_nonneg _) ((abs_nonneg _).trans hetaT)
  exact ⟨hf.bdd_mul heta hetaNorm,
    by simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hnorm⟩

theorem tendsto_integral_mul_of_uniform_abs_bound_div
    {F : ℝ → T → ℝ} (hF : ∀ r : ℝ, 0 < r → Integrable (F r) μ)
    {C : ℝ} (hbound : ∀ r : ℝ, 0 < r → ∀ᵐ t ∂μ, |F r t| ≤ C / r)
    {eta : T → ℝ} (heta : AEStronglyMeasurable eta μ)
    {K : ℝ} (hetabound : ∀ᵐ t ∂μ, |eta t| ≤ K)
    {ι : Type*} {l : Filter ι} {R : ι → ℝ} (hR : Tendsto R l atTop) :
    Tendsto (fun i => ∫ t, eta t * F (R i) t ∂μ) l (𝓝 0) := by
  have hlarge : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop 0)
  have hb : ∀ᶠ i in l,
      ‖∫ t, eta t * F (R i) t ∂μ‖ ≤ K * (C / R i) * μ.real univ := by
    filter_upwards [hlarge] with i hi
    simpa only [Real.norm_eq_abs] using
      (integrable_mul_and_abs_integral_le_of_ae_abs_le
        (hF (R i) hi) heta (hbound (R i) hi) hetabound).2
  apply squeeze_zero_norm' hb
  have hz := ((hR.const_div_atTop C).const_mul K).mul_const (μ.real univ)
  simpa only [mul_zero, zero_mul] using hz

end MeasureTheory
