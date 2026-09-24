import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LiminfLimsup

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

theorem integrable_of_tendsto_integral_of_eventually_le
    {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {F : ℕ → A → ℝ} {f B : A → ℝ} {L : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hB : Integrable B μ)
    (hF_le : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, F n x ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 L)) :
    Integrable f μ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hF_le
  let G : ℕ → A → ℝ := fun n x => B x - F (n + N) x
  have hG : ∀ n, Integrable (G n) μ := fun n => hB.sub (hF (n + N))
  have hG_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ G n x := fun n =>
    (hN (n + N) (Nat.le_add_left N n)).mono fun x hx => sub_nonneg.mpr hx
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (B x - f x)) := by
    filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.sub (hx.comp (tendsto_add_atTop_nat N))
  have hGintegral : ∀ n, (∫⁻ x, ‖G n x‖ₑ ∂μ) =
      ENNReal.ofReal ((∫ x, B x ∂μ) - ∫ x, F (n + N) x ∂μ) := by
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hG n)]
    congr 1
    calc
      (∫ x, ‖G n x‖ ∂μ) = ∫ x, G n x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hG_nonneg n] with x hx
        exact Real.norm_of_nonneg hx
      _ = _ := integral_sub hB (hF (n + N))
  have hGintlim : Tendsto (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop
      (𝓝 (ENNReal.ofReal ((∫ x, B x ∂μ) - L))) := by
    simp_rw [hGintegral]
    exact ENNReal.tendsto_ofReal
      (tendsto_const_nhds.sub (hint.comp (tendsto_add_atTop_nat N)))
  have hGfin : Integrable (fun x => B x - f x) μ := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hG n).aestronglyMeasurable) hGlim, ?_⟩
    calc
      (∫⁻ x, ‖B x - f x‖ₑ ∂μ) = ∫⁻ x, liminf (fun n => ‖G n x‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hGlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hG n).aestronglyMeasurable.aemeasurable.enorm)
      _ < ⊤ := by rw [hGintlim.liminf_eq]; exact ENNReal.ofReal_lt_top
  have hfinal : Integrable (fun x => B x - (B x - f x)) μ := hB.sub hGfin
  simpa only [sub_sub_cancel] using hfinal

end MeasureTheory
