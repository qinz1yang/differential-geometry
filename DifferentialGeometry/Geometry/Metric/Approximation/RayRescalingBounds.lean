import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace GC.MetricGeometry

theorem strong_edge_ray_rescaling_bounds {Δ s η c d a h e θ : ℝ}
    (hΔ : 1 ≤ Δ) (hs : 0 < s) (hs1 : s < 1 / 100) (hη : 0 < η)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2)
    (hd : d ≤ 13 * Δ + 1) (ha : a ≤ Δ / 2)
    (he : e ≤ s / 1000) (hθ : θ ≤ s / 1000) (hh : h ≤ 2 * e + θ) :
    let D := max (201 * Δ) (4 / s)
    200 * Δ < D ∧ d + s⁻¹ / c ≤ η⁻¹ ∧ s⁻¹ / c + a + η ≤ η⁻¹ ∧
      3 * c * η + c * h ≤ s ∧ s⁻¹ + c * h + c * η ≤ D := by
  have hΔ0 : 0 < Δ := by linarith
  have hc0 : 0 < c := by linarith [hc.1]
  have hi : 0 < s⁻¹ := inv_pos.mpr hs
  have hηi : 0 < η⁻¹ := inv_pos.mpr hη
  have hboundΔ : 100000 * Δ ≤ η⁻¹ := by
    have hh' := (le_div_iff₀ (by positivity : 0 < 100000 * Δ)).mp hηΔ
    rw [← one_div η]
    apply (le_div_iff₀ hη).mpr
    nlinarith
  have hbounds : 1000 * s⁻¹ ≤ η⁻¹ := by
    rw [← one_div η]
    apply (le_div_iff₀ hη).mpr
    have he' : 1000 * η ≤ s := by linarith
    have hm := mul_le_mul_of_nonneg_right he' hi.le
    rw [mul_inv_cancel₀ hs.ne'] at hm
    nlinarith
  have hdiv : s⁻¹ / c ≤ 2 * s⁻¹ := by
    apply (div_le_iff₀ hc0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc.1 hi.le]
  have hsmall : η ≤ 1 := by linarith
  have hdomain1 : d + s⁻¹ / c ≤ η⁻¹ := by linarith
  have hdomain2 : s⁻¹ / c + a + η ≤ η⁻¹ := by linarith
  have hhe : h ≤ 3 * s / 1000 := by linarith
  have hch : c * h ≤ 6 * s / 1000 := by
    have h1 := mul_le_mul_of_nonneg_left hhe hc0.le
    have h2 := mul_le_mul_of_nonneg_right hc.2 hs.le
    nlinarith
  have hcη : c * η ≤ 2 * s / 1000 := by
    have h1 := mul_le_mul_of_nonneg_left hηs hc0.le
    have h2 := mul_le_mul_of_nonneg_right hc.2 hs.le
    nlinarith
  have hsi : s < s⁻¹ := by
    rw [← one_div s]
    apply (lt_div_iff₀ hs).mpr
    nlinarith
  refine ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), hdomain1, hdomain2, ?_, ?_⟩
  · nlinarith
  · apply le_trans _ (le_max_right _ _)
    rw [div_eq_mul_inv]
    linarith

end GC.MetricGeometry
