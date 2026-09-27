import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem isProbabilityMeasure_withDensity_ofReal {k : α → ℝ}
    (hk_nonneg : 0 ≤ᵐ[μ] k) (hk_one : ∫ x, k x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (k x))) := by
  have hk : Integrable k μ := Integrable.of_integral_ne_zero (by rw [hk_one]; exact one_ne_zero)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hk hk_nonneg, hk_one, ENNReal.ofReal_one]

theorem ae_withDensity_of_support_subset {k : α → ℝ} {s : Set α} {P : α → Prop}
    (hk : AEMeasurable k μ) (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hP : ∀ᵐ x ∂μ.restrict s, P x) :
    ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (k x)), P x := by
  apply (ae_withDensity_iff' hk.ennreal_ofReal).mpr
  filter_upwards [(ae_restrict_iff' hs).mp hP] with x hx hdx
  apply hx
  apply hks
  intro hkx
  exact hdx (by simp [hkx])

theorem withDensity_ofReal_le_const_smul_restrict {k : α → ℝ} {s : Set α}
    {C : ℝ} (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) :
    μ.withDensity (fun x => ENNReal.ofReal (k x)) ≤ ENNReal.ofReal C • μ.restrict s := by
  have hle : (fun x => ENNReal.ofReal (k x)) ≤ᵐ[μ]
      s.indicator (fun _ => ENNReal.ofReal C) := by
    filter_upwards [] with x
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx] using ENNReal.ofReal_le_ofReal (hkC x hx)
    · have hkx : k x = 0 := by
        by_contra hkx
        exact hx (hks hkx)
      simp only [hkx, ENNReal.ofReal_zero, Set.indicator_of_notMem hx, le_refl]
  simpa only [withDensity_indicator hs, withDensity_const] using withDensity_mono hle

variable {F : Type*} [NormedAddCommGroup F]

theorem integrable_withDensity_ofReal_of_support_subset {k : α → ℝ} {s : Set α}
    {f : α → F} {C : ℝ} (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) (hf : IntegrableOn f s μ) :
    Integrable f (μ.withDensity (fun x => ENNReal.ofReal (k x))) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure
    (withDensity_ofReal_le_const_smul_restrict hs hks hkC)

theorem integral_withDensity_ofReal_le_const_mul_setIntegral {k h : α → ℝ} {s : Set α}
    {C : ℝ} (hk : Measurable k) (hk_nonneg : ∀ x, 0 ≤ k x)
    (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) (hh : IntegrableOn h s μ)
    (hh_nonneg : 0 ≤ᵐ[μ.restrict s] h) :
    (∫ x, h x ∂μ.withDensity (fun x => ENNReal.ofReal (k x))) ≤
      C * ∫ x in s, h x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk_nonneg _), smul_eq_mul]
  have hzero : ∀ x, x ∉ s → k x * h x = 0 := by
    intro x hx
    have hkx : k x = 0 := by
      by_contra hkx
      exact hx (hks hkx)
    rw [hkx, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← integral_const_mul]
  have hkh : IntegrableOn (fun x => k x * h x) s μ := by
    have hint := integrable_withDensity_ofReal_of_support_subset hs hks hkC hh
    have hprod := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hint
    simp only [ENNReal.toReal_ofReal (hk_nonneg _), smul_eq_mul] at hprod
    exact hprod.integrableOn
  apply integral_mono_ae hkh (hh.const_mul C)
  filter_upwards [ae_restrict_mem hs, hh_nonneg] with x hx hhx
  exact mul_le_mul_of_nonneg_right (hkC x hx) hhx

end MeasureTheory

end
