import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}

def CrossAnti (R : ℝ) (f g : ℝ → ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b

theorem lintegral_cross_le {s : ℝ}
    (hf : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) R)))
    (hg : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) R)))
    (hcross : CrossAnti R f g) (hs : 0 ≤ s) (hsR : s ≤ R) :
    (∫⁻ t in Ioc (0 : ℝ) R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * ∫⁻ t in Ioc (0 : ℝ) R, g t ∂μ := by
  have hAm : MeasurableSet (Ioc (0 : ℝ) s) := measurableSet_Ioc
  have hBm : MeasurableSet (Ioc s R) := measurableSet_Ioc
  have hdisj : Disjoint (Ioc (0 : ℝ) s) (Ioc s R) := Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Ioc (0 : ℝ) s ∪ Ioc s R = Ioc (0 : ℝ) R := Ioc_union_Ioc_eq_Ioc hs hsR
  have hAsub : Ioc (0 : ℝ) s ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc le_rfl hsR
  have hBsub : Ioc s R ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc hs le_rfl
  have hfA : AEMeasurable f (μ.restrict (Ioc (0 : ℝ) s)) :=
    hf.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hfB : AEMeasurable f (μ.restrict (Ioc s R)) :=
    hf.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hgA : AEMeasurable g (μ.restrict (Ioc (0 : ℝ) s)) :=
    hg.mono_measure (Measure.restrict_mono hAsub le_rfl)
  have hgB : AEMeasurable g (μ.restrict (Ioc s R)) :=
    hg.mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hf_split : ∫⁻ t in Ioc (0 : ℝ) R, f t ∂μ
      = (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) + ∫⁻ t in Ioc s R, f t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  have hg_split : ∫⁻ t in Ioc (0 : ℝ) R, g t ∂μ
      = (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ) + ∫⁻ t in Ioc s R, g t ∂μ := by
    rw [← hunion]; exact lintegral_union hBm hdisj
  have hstar : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
      ≤ (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * ∫⁻ t in Ioc s R, g t ∂μ := by
    have e1 : (∫⁻ t in Ioc s R, f t ∂μ) * (∫⁻ t in Ioc (0 : ℝ) s, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0 : ℝ) s, f b * g a ∂μ ∂μ := by
      rw [← lintegral_mul_const'' _ hfB]
      exact lintegral_congr fun b => (lintegral_const_mul'' _ hgA).symm
    have e2 : (∫⁻ t in Ioc (0 : ℝ) s, f t ∂μ) * (∫⁻ t in Ioc s R, g t ∂μ)
        = ∫⁻ b in Ioc s R, ∫⁻ a in Ioc (0 : ℝ) s, f a * g b ∂μ ∂μ := by
      rw [← lintegral_const_mul'' _ hgB]
      exact lintegral_congr fun b => (lintegral_mul_const'' _ hfA).symm
    rw [e1, e2]
    refine lintegral_mono_ae ((ae_restrict_mem hBm).mono fun b hb => ?_)
    exact lintegral_mono_ae ((ae_restrict_mem hAm).mono fun a ha =>
      hcross a b ha.1 (ha.2.trans hb.1.le) hb.2)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar

theorem crossAnti_ofReal {F G : ℝ → ℝ}
    (hanti : AntitoneOn (fun t => F t / G t) (Ioc (0 : ℝ) R))
    (hF : ∀ ⦃t⦄, t ∈ Ioc (0 : ℝ) R → 0 ≤ F t)
    (hG : ∀ ⦃t⦄, t ∈ Ioc (0 : ℝ) R → 0 < G t) :
    CrossAnti R (fun t => ENNReal.ofReal (F t)) (fun t => ENNReal.ofReal (G t)) := by
  intro a b ha hab hbR
  have hbmem : b ∈ Ioc (0 : ℝ) R := ⟨ha.trans_le hab, hbR⟩
  have hamem : a ∈ Ioc (0 : ℝ) R := ⟨ha, hab.trans hbR⟩
  have hdiv : F b / G b ≤ F a / G a := hanti hamem hbmem hab
  have hcross : F b * G a ≤ F a * G b :=
    (div_le_div_iff₀ (hG hbmem) (hG hamem)).1 hdiv
  calc ENNReal.ofReal (F b) * ENNReal.ofReal (G a)
      = ENNReal.ofReal (F b * G a) := (ENNReal.ofReal_mul (hF hbmem)).symm
    _ ≤ ENNReal.ofReal (F a * G b) := ENNReal.ofReal_le_ofReal hcross
    _ = ENNReal.ofReal (F a) * ENNReal.ofReal (G b) := ENNReal.ofReal_mul (hF hamem)

theorem crossAnti_indicator (h : CrossAnti R f g) (τ : ℝ) :
    CrossAnti R (Set.indicator (Iio τ) f) g := by
  intro a b ha hab hbR
  by_cases hbτ : b ∈ Iio τ
  · have haτ : a ∈ Iio τ := lt_of_le_of_lt hab hbτ
    rw [Set.indicator_of_mem hbτ, Set.indicator_of_mem haτ]
    exact h a b ha hab hbR
  · rw [Set.indicator_of_notMem hbτ, zero_mul]
    exact zero_le _

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
