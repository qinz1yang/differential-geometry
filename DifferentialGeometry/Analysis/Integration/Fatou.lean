import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

theorem tendsto_integral_le_integral_of_nonpos
    {A : Type*} [MeasurableSpace A] {mu : Measure A}
    {F : Nat → A → Real} {f : A → Real} {L : Real}
    (hF : ∀ n, Integrable (F n) mu) (hf : Integrable f mu)
    (hF_nonpos : ∀ n, ∀ᵐ x ∂mu, F n x ≤ 0)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n ↦ ∫ x, F n x ∂mu) atTop (𝓝 L)) :
    L ≤ ∫ x, f x ∂mu := by
  have hall : ∀ᵐ x ∂mu, ∀ n, F n x ≤ 0 :=
    ae_all_iff.mpr hF_nonpos
  have hf_nonpos : ∀ᵐ x ∂mu, f x ≤ 0 := by
    filter_upwards [hall, hlim] with x hx hxlim
    exact le_of_tendsto hxlim (Eventually.of_forall hx)
  have hL : L ≤ 0 := le_of_tendsto hint
    (Eventually.of_forall fun n ↦ integral_nonpos_of_ae (hF_nonpos n))
  have hfatou := lintegral_liminf_le' (μ := mu) (u := atTop)
    (f := fun n x ↦ ENNReal.ofReal (-F n x))
    (fun n ↦ ENNReal.measurable_ofReal.comp_aemeasurable
      (hF n).neg.aestronglyMeasurable.aemeasurable)
  have hpoint : (fun x ↦ liminf (fun n ↦ ENNReal.ofReal (-F n x)) atTop) =ᵐ[mu]
      (fun x ↦ ENNReal.ofReal (-f x)) := by
    filter_upwards [hlim] with x hx
    exact (ENNReal.tendsto_ofReal hx.neg).liminf_eq
  have hlimint : Tendsto (fun n ↦ ∫⁻ x, ENNReal.ofReal (-F n x) ∂mu)
      atTop (𝓝 (ENNReal.ofReal (-L))) := by
    have heq : (fun n ↦ ∫⁻ x, ENNReal.ofReal (-F n x) ∂mu) =
        (fun n ↦ ENNReal.ofReal (-(∫ x, F n x ∂mu))) := by
      funext n
      have heq := ofReal_integral_eq_lintegral_ofReal (hF n).neg
        ((hF_nonpos n).mono fun x hx ↦ neg_nonneg.mpr hx)
      simpa only [Pi.neg_apply, integral_neg] using heq.symm
    rw [heq]
    exact ENNReal.tendsto_ofReal hint.neg
  rw [lintegral_congr_ae hpoint, hlimint.liminf_eq] at hfatou
  have hfeq := ofReal_integral_eq_lintegral_ofReal hf.neg
    (hf_nonpos.mono fun x hx ↦ neg_nonneg.mpr hx)
  simp only [Pi.neg_apply, integral_neg] at hfeq
  rw [← hfeq] at hfatou
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hfatou
  rw [ENNReal.toReal_ofReal (neg_nonneg.mpr (integral_nonpos_of_ae hf_nonpos)),
    ENNReal.toReal_ofReal (neg_nonneg.mpr hL)] at hreal
  linarith

theorem tendsto_integral_le_integral_of_eventually_le
    {A : Type*} [MeasurableSpace A] {mu : Measure A}
    {F : Nat → A → Real} {f B : A → Real} {L : Real}
    (hF : ∀ n, Integrable (F n) mu) (hf : Integrable f mu) (hB : Integrable B mu)
    (hF_le : ∀ᶠ n in atTop, ∀ᵐ x ∂mu, F n x ≤ B x)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n ↦ ∫ x, F n x ∂mu) atTop (𝓝 L)) :
    L ≤ ∫ x, f x ∂mu := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hF_le
  have hlimsub : ∀ᵐ x ∂mu, Tendsto (fun n ↦ F (n + N) x - B x)
      atTop (𝓝 (f x - B x)) := by
    filter_upwards [hlim] with x hx
    exact (hx.comp (tendsto_add_atTop_nat N)).sub_const (B x)
  have hintsub : Tendsto (fun n ↦ ∫ x, F (n + N) x - B x ∂mu)
      atTop (𝓝 (L - ∫ x, B x ∂mu)) := by
    have hraw := (hint.comp (tendsto_add_atTop_nat N)).sub_const (∫ x, B x ∂mu)
    apply hraw.congr
    intro n
    exact (integral_sub (hF (n + N)) hB).symm
  have hbound := tendsto_integral_le_integral_of_nonpos
    (fun n ↦ (hF (n + N)).sub hB) (hf.sub hB)
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).mono
      fun x hx ↦ sub_nonpos.mpr hx) hlimsub hintsub
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub hf hB] at hbound
  linarith

end MeasureTheory

end
