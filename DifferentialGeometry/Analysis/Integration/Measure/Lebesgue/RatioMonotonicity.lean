import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Disjoint

open Set
open scoped ENNReal

namespace MeasureTheory

theorem setLIntegral_mul_setLIntegral_le_of_forall_mul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (hf : AEMeasurable f (μ.restrict t))
    (hg : AEMeasurable g (μ.restrict t))
    (hcross : ∀ a ∈ s, ∀ b ∈ t \ s, f b * g a ≤ f a * g b) :
    (∫⁻ x in t, f x ∂μ) * (∫⁻ x in s, g x ∂μ) ≤
      (∫⁻ x in s, f x ∂μ) * ∫⁻ x in t, g x ∂μ := by
  have hdiff : MeasurableSet (t \ s) := ht.diff hs
  have hdisj : Disjoint s (t \ s) := disjoint_sdiff_right
  have hunion : s ∪ (t \ s) = t := union_sdiff_cancel hst
  have hfA := hf.mono_measure (Measure.restrict_mono hst le_rfl)
  have hfB := hf.mono_measure (Measure.restrict_mono (show t \ s ⊆ t from sdiff_subset) le_rfl)
  have hgA := hg.mono_measure (Measure.restrict_mono hst le_rfl)
  have hgB := hg.mono_measure (Measure.restrict_mono (show t \ s ⊆ t from sdiff_subset) le_rfl)
  have hf_split : ∫⁻ x in t, f x ∂μ =
      (∫⁻ x in s, f x ∂μ) + ∫⁻ x in t \ s, f x ∂μ := by
    conv_lhs => rw [← hunion]
    exact lintegral_union hdiff hdisj
  have hg_split : ∫⁻ x in t, g x ∂μ =
      (∫⁻ x in s, g x ∂μ) + ∫⁻ x in t \ s, g x ∂μ := by
    conv_lhs => rw [← hunion]
    exact lintegral_union hdiff hdisj
  have hstar : (∫⁻ x in t \ s, f x ∂μ) * (∫⁻ x in s, g x ∂μ) ≤
      (∫⁻ x in s, f x ∂μ) * ∫⁻ x in t \ s, g x ∂μ := by
    have hleft : (∫⁻ x in t \ s, f x ∂μ) * (∫⁻ x in s, g x ∂μ) =
        ∫⁻ b in t \ s, ∫⁻ a in s, f b * g a ∂μ ∂μ := by
      rw [← lintegral_mul_const'' _ hfB]
      exact lintegral_congr fun b => (lintegral_const_mul'' _ hgA).symm
    have hright : (∫⁻ x in s, f x ∂μ) * (∫⁻ x in t \ s, g x ∂μ) =
        ∫⁻ b in t \ s, ∫⁻ a in s, f a * g b ∂μ ∂μ := by
      rw [← lintegral_const_mul'' _ hgB]
      exact lintegral_congr fun b => (lintegral_mul_const'' _ hfA).symm
    rw [hleft, hright]
    refine lintegral_mono_ae ((ae_restrict_mem hdiff).mono fun b hb => ?_)
    exact lintegral_mono_ae ((ae_restrict_mem hs).mono fun a ha => hcross a ha b hb)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar

theorem setLIntegral_Iic_mul_setLIntegral_Iic_le
    {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [ClosedIicTopology α]
    {μ : Measure α} {f g : α → ℝ≥0∞} {s R : α}
    (hf : AEMeasurable f (μ.restrict (Iic R)))
    (hg : AEMeasurable g (μ.restrict (Iic R)))
    (hcross : ∀ ⦃a b : α⦄, a ≤ b → b ≤ R → f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ x in Iic R, f x ∂μ) * (∫⁻ x in Iic s, g x ∂μ) ≤
      (∫⁻ x in Iic s, f x ∂μ) * ∫⁻ x in Iic R, g x ∂μ := by
  apply setLIntegral_mul_setLIntegral_le_of_forall_mul_le measurableSet_Iic
    measurableSet_Iic (Iic_subset_Iic.mpr hsR) hf hg
  intro a ha b hb
  exact hcross (ha.trans (lt_of_not_ge hb.2).le) hb.1

theorem setLIntegral_Ioc_mul_setLIntegral_Ioc_le
    {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [ClosedIicTopology α]
    {μ : Measure α} {f g : α → ℝ≥0∞} {l s R : α}
    (hf : AEMeasurable f (μ.restrict (Ioc l R)))
    (hg : AEMeasurable g (μ.restrict (Ioc l R)))
    (hcross : ∀ ⦃a b : α⦄, l < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ x in Ioc l R, f x ∂μ) * (∫⁻ x in Ioc l s, g x ∂μ) ≤
      (∫⁻ x in Ioc l s, f x ∂μ) * ∫⁻ x in Ioc l R, g x ∂μ := by
  apply setLIntegral_mul_setLIntegral_le_of_forall_mul_le measurableSet_Ioc
    measurableSet_Ioc (Ioc_subset_Ioc le_rfl hsR) hf hg
  intro a ha b hb
  have hsb : s < b := lt_of_not_ge (fun hbs => hb.2 ⟨hb.1.1, hbs⟩)
  exact hcross ha.1 (ha.2.trans hsb.le) hb.1.2

end MeasureTheory
