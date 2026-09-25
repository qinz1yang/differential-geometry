import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

end

noncomputable section

namespace DifferentialGeometry.Analysis

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f g : α → ℝ}

theorem lowerBoundedIntegral_add_measure
    (hf : AEStronglyMeasurable f (μ + ν)) (hg : Integrable g (μ + ν))
    (hgf : g ≤ᵐ[μ + ν] f) :
    lowerBoundedIntegral f g (μ + ν) =
      lowerBoundedIntegral f g μ + lowerBoundedIntegral f g ν := by
  obtain ⟨hfμ, hfν⟩ := aestronglyMeasurable_add_measure_iff.mp hf
  obtain ⟨hgμ, hgν⟩ := integrable_add_measure.mp hg
  obtain ⟨hleμ, hleν⟩ := ae_add_measure_iff.mp hgf
  by_cases hiμ : Integrable f μ
  · by_cases hiν : Integrable f ν
    · rw [lowerBoundedIntegral_eq_integral (hiμ.add_measure hiν) hg hgf,
        lowerBoundedIntegral_eq_integral hiμ hgμ hleμ,
        lowerBoundedIntegral_eq_integral hiν hgν hleν,
        integral_add_measure hiμ hiν, WithTop.coe_add]
    · rw [(lowerBoundedIntegral_eq_top_iff hfν hgν hleν).2 hiν,
        WithTop.add_top, lowerBoundedIntegral_eq_top_iff hf hg hgf]
      exact fun h ↦ hiν h.right_of_add_measure
  · rw [(lowerBoundedIntegral_eq_top_iff hfμ hgμ hleμ).2 hiμ,
      WithTop.top_add, lowerBoundedIntegral_eq_top_iff hf hg hgf]
    exact fun h ↦ hiμ h.left_of_add_measure

theorem lowerBoundedIntegral_Ioo_add {μ : Measure ℝ} [NullSingletonClass μ]
    {f g : ℝ → ℝ} {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : AEStronglyMeasurable f (μ.restrict (Set.Ioo a b)))
    (hg : Integrable g (μ.restrict (Set.Ioo a b)))
    (hgf : g ≤ᵐ[μ.restrict (Set.Ioo a b)] f) :
    lowerBoundedIntegral f g (μ.restrict (Set.Ioo a b)) =
      lowerBoundedIntegral f g (μ.restrict (Set.Ioo a c)) +
        lowerBoundedIntegral f g (μ.restrict (Set.Ioo c b)) := by
  have hμ : μ.restrict (Set.Ioo a b) =
      μ.restrict (Set.Ioo a c) + μ.restrict (Set.Ioo c b) := by
    simp only [restrict_Ioo_eq_restrict_Ioc]
    rw [← Set.Ioc_union_Ioc_eq_Ioc hac hcb,
      Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  rw [hμ] at hf hg hgf ⊢
  exact lowerBoundedIntegral_add_measure hf hg hgf

end DifferentialGeometry.Analysis
