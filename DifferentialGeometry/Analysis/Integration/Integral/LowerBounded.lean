import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

noncomputable section

namespace DifferentialGeometry.Analysis

open MeasureTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}

def lowerBoundedIntegral (f g : α → ℝ) (μ : Measure α) : WithTop ℝ :=
  if (∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ) = ∞ then ⊤ else
    ↑((∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ).toReal + ∫ x, g x ∂μ)

theorem lowerBoundedIntegral_eq_integral (hf : Integrable f μ) (hg : Integrable g μ)
    (hgf : g ≤ᵐ[μ] f) : lowerBoundedIntegral f g μ = (↑(∫ x, f x ∂μ) : WithTop ℝ) := by
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ f x - g x) := hgf.mono fun x hx ↦ sub_nonneg.mpr hx
  have hi : 0 ≤ ∫ x, f x - g x ∂μ := integral_nonneg_of_ae hnonneg
  have hsub : Integrable (fun x ↦ f x - g x) μ := hf.sub hg
  unfold lowerBoundedIntegral
  rw [← ofReal_integral_eq_lintegral_ofReal hsub hnonneg]
  simp only [ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal hi]
  rw [integral_sub hf hg, sub_add_cancel]

theorem lowerBoundedIntegral_eq_top_iff (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ) (hgf : g ≤ᵐ[μ] f) :
    lowerBoundedIntegral f g μ = ⊤ ↔ ¬ Integrable f μ := by
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ f x - g x) := hgf.mono fun x hx ↦ sub_nonneg.mpr hx
  have hi : Integrable (fun x ↦ f x - g x) μ ↔ Integrable f μ := by
    constructor
    · intro h
      have hh : Integrable (fun x ↦ (f x - g x) + g x) μ := h.add hg
      simpa only [sub_add_cancel] using hh
    · exact fun h ↦ h.sub hg
  have hm : AEStronglyMeasurable (fun x ↦ f x - g x) μ :=
    hf.sub hg.aestronglyMeasurable
  have heq := not_congr ((lintegral_ofReal_ne_top_iff_integrable hm hnonneg).trans hi)
  simpa [lowerBoundedIntegral] using heq

theorem lowerBoundedIntegral_congr_lower_bound (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) (hgf : g ≤ᵐ[μ] f) (hhf : h ≤ᵐ[μ] f) :
    lowerBoundedIntegral f g μ = lowerBoundedIntegral f h μ := by
  by_cases hi : Integrable f μ
  · rw [lowerBoundedIntegral_eq_integral hi hg hgf,
      lowerBoundedIntegral_eq_integral hi hh hhf]
  · rw [(lowerBoundedIntegral_eq_top_iff hf hg hgf).2 hi,
      (lowerBoundedIntegral_eq_top_iff hf hh hhf).2 hi]

end DifferentialGeometry.Analysis
