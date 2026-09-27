import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

theorem tendsto_integral_mul_of_tendstoUniformly_of_integral_norm_bounded
    {A X : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter A}
    {K f : A → X → ℝ} {f₀ : X → ℝ} {L C : ℝ}
    (hK : ∀ᶠ a in l, Integrable (K a) μ)
    (hif : ∀ᶠ a in l, Integrable (fun x => K a x * f a x) μ)
    (hi₀ : ∀ᶠ a in l, Integrable (fun x => K a x * f₀ x) μ)
    (hbound : ∀ᶠ a in l, (∫ x, ‖K a x‖ ∂μ) ≤ C)
    (hf : TendstoUniformly f f₀ l)
    (hlim : Tendsto (fun a => ∫ x, K a x * f₀ x ∂μ) l (𝓝 L)) :
    Tendsto (fun a => ∫ x, K a x * f a x ∂μ) l (𝓝 L) := by
  have hdiff : Tendsto (fun a => (∫ x, K a x * f a x ∂μ) -
      ∫ x, K a x * f₀ x ∂μ) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let B := max C 1
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have hδ : 0 < ε / (2 * B) := div_pos hε (mul_pos (by norm_num) hB)
    have hu := Metric.tendstoUniformly_iff.mp hf (ε / (2 * B)) hδ
    filter_upwards [hK, hif, hi₀, hbound, hu] with a hk hi hi0 hb ha
    rw [dist_zero_right, ← integral_sub hi hi0]
    have heq : (fun x => K a x * f a x - K a x * f₀ x) =
        fun x => K a x * (f a x - f₀ x) := by funext x; ring
    rw [heq]
    have hnorm := norm_integral_le_of_norm_le (hk.norm.mul_const (ε / (2 * B)))
      (show ∀ᵐ x ∂μ, ‖K a x * (f a x - f₀ x)‖ ≤
          ‖K a x‖ * (ε / (2 * B)) from by
        filter_upwards with x
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [dist_eq_norm, norm_sub_rev] using (ha x).le)
    rw [integral_mul_const] at hnorm
    have hb' : (∫ x, ‖K a x‖ ∂μ) ≤ B := hb.trans (le_max_left _ _)
    have he : B * (ε / (2 * B)) = ε / 2 := by field_simp
    exact lt_of_le_of_lt (hnorm.trans ((mul_le_mul_of_nonneg_right hb' hδ.le).trans_eq he))
      (half_lt_self hε)
  have hsum := hdiff.add hlim
  simpa only [sub_add_cancel, zero_add] using hsum

end MeasureTheory
