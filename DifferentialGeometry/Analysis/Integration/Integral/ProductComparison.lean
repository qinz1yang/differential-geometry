import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

namespace MeasureTheory

theorem integrable_prod_and_integral_le_of_fiber_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [SFinite ν] [SFinite μ]
    {F G H : T × X → ℝ} (hFmeas : AEStronglyMeasurable F (ν.prod μ))
    (hG : Integrable G (ν.prod μ)) (hH : Integrable H (ν.prod μ))
    (hF : ∀ᵐ t ∂ν, Integrable (fun x => F (t, x)) μ)
    (hFG : ∀ᵐ p ∂ν.prod μ, F p ≤ G p)
    (hHF : ∀ᵐ t ∂ν, (∫ x, H (t, x) ∂μ) ≤ ∫ x, F (t, x) ∂μ) :
    Integrable F (ν.prod μ) ∧ (∫ p, H p ∂ν.prod μ) ≤ ∫ p, F p ∂ν.prod μ := by
  have hmajor : Integrable
      (fun t => 2 * (∫ x, ‖G (t, x)‖ ∂μ) - ∫ x, H (t, x) ∂μ) ν :=
    (hG.integral_norm_prod_left.const_mul 2).sub hH.integral_prod_left
  have hnorm : Integrable (fun t => ∫ x, ‖F (t, x)‖ ∂μ) ν := by
    apply hmajor.mono' hFmeas.norm.integral_prod_right'
    filter_upwards [hF, hG.prod_right_ae, Measure.ae_ae_of_ae_prod hFG, hHF] with t ht htG htFG htHF
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F (t, x)))]
    have hbound : (∫ x, ‖F (t, x)‖ ∂μ) ≤
        ∫ x, 2 * ‖G (t, x)‖ - F (t, x) ∂μ := by
      apply integral_mono_ae ht.norm ((htG.norm.const_mul 2).sub ht)
      filter_upwards [htFG] with x hx
      change ‖F (t, x)‖ ≤ 2 * ‖G (t, x)‖ - F (t, x)
      have hGnorm : G (t, x) ≤ ‖G (t, x)‖ := le_abs_self _
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · linarith [norm_nonneg (G (t, x))]
      · linarith
    rw [integral_sub (htG.norm.const_mul 2) ht, integral_const_mul] at hbound
    linarith
  have hFprod : Integrable F (ν.prod μ) := (integrable_prod_iff hFmeas).mpr ⟨hF, hnorm⟩
  refine ⟨hFprod, ?_⟩
  rw [integral_prod H hH, integral_prod F hFprod]
  exact integral_mono_ae hH.integral_prod_left hFprod.integral_prod_left hHF

end MeasureTheory
