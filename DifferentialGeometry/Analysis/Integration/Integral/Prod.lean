import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Module.Dual

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]

private theorem integral_prod_nonneg {f : α × β → ℝ}
    (hf : Integrable f (μ.prod ν)) (hpos : 0 ≤ᵐ[μ.prod ν] f) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  have hslice := (integrable_prod_iff hf.aestronglyMeasurable).mp hf
  have hpos_slice := Measure.ae_ae_of_ae_prod hpos
  have houter_pos : 0 ≤ᵐ[μ] fun x => ∫ y, f (x, y) ∂ν := by
    filter_upwards [hpos_slice] with x hx
    exact integral_nonneg_of_ae hx
  rw [integral_eq_lintegral_of_nonneg_ae hpos hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae houter_pos hf.integral_prod_left.aestronglyMeasurable,
    lintegral_prod _ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hslice.1, hpos_slice] with x hx hxp
  exact (ofReal_integral_eq_lintegral_ofReal hx hxp).symm

private theorem integral_prod_real {f : α × β → ℝ} (hf : Integrable f (μ.prod ν)) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  have hp := hf.pos_part
  have hn := hf.neg_part
  have hps := (integrable_prod_iff hp.aestronglyMeasurable).mp hp
  have hns := (integrable_prod_iff hn.aestronglyMeasurable).mp hn
  calc
    ∫ p, f p ∂μ.prod ν =
        (∫ p, max (f p) 0 ∂μ.prod ν) - ∫ p, max (-f p) 0 ∂μ.prod ν := by
      rw [← integral_sub hp hn]
      simp only [max_zero_sub_max_neg_zero_eq_self]
    _ = (∫ x, ∫ y, max (f (x, y)) 0 ∂ν ∂μ) -
        ∫ x, ∫ y, max (-f (x, y)) 0 ∂ν ∂μ := by
      rw [integral_prod_nonneg hp (Filter.Eventually.of_forall fun _ => le_max_right _ _),
        integral_prod_nonneg hn (Filter.Eventually.of_forall fun _ => le_max_right _ _)]
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
      rw [← integral_sub hp.integral_prod_left hn.integral_prod_left]
      apply integral_congr_ae
      filter_upwards [hps.1, hns.1] with x hxp hxn
      rw [← integral_sub hxp hxn]
      simp only [max_zero_sub_max_neg_zero_eq_self]

theorem Integrable.integral_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : α × β → F} (hf : Integrable f (μ.prod ν)) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  by_cases hF : CompleteSpace F
  · let _ := hF
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    rw [← L.integral_comp_comm hf, ← L.integral_comp_comm hf.integral_prod_left,
      integral_prod_real (L.integrable_comp hf)]
    apply integral_congr_ae
    filter_upwards [(integrable_prod_iff hf.aestronglyMeasurable).mp hf |>.1] with x hx
    exact L.integral_comp_comm hx
  · simp only [integral_of_not_completeSpace hF]

open Set in
theorem integral_eq_integral_restrict_prod_of_support
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SFinite μ] {s : Set α} {t : Set β}
    {f : α × β → E}
    (hfs : ∀ p, p ∉ s ×ˢ t → f p = 0) :
    (∫ p, f p ∂μ.prod ν) = ∫ p, f p ∂(μ.restrict s).prod (ν.restrict t) := by
  rw [Measure.prod_restrict]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  exact hfs p hp

open Set in
theorem integral_eq_integral_restrict_prod_of_support_subset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SFinite μ]
    {s : Set α} {t t₀ : Set β} (ht : MeasurableSet t₀) (hsub : t₀ ⊆ t)
    {f : α × β → E}
    (hfs : ∀ p, p ∉ s ×ˢ t₀ → f p = 0) :
    (∫ p, f p ∂μ.prod (ν.restrict t)) =
      ∫ p, f p ∂(μ.restrict s).prod (ν.restrict t₀) := by
  have h := integral_eq_integral_restrict_prod_of_support
    (μ := μ) (ν := ν.restrict t) hfs
  rwa [Measure.restrict_restrict ht, inter_eq_left.mpr hsub] at h


end MeasureTheory
