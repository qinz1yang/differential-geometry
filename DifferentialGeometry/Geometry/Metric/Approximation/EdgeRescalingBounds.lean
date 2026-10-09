import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace GC.MetricGeometry

private theorem rescale_domain_budget {R c ε δ : ℝ}
    (hR : 0 ≤ R) (hc : 1 / 2 < c) (hε : 0 < ε) (hδ : 0 < δ)
    (hδone : δ < 1) (hεsmall : ε < δ / 100000) (hRδ : R * δ ≤ 1) :
    R + δ⁻¹ / c + 2 * ε ≤ ε⁻¹ := by
  have hc0 : 0 < c := by linarith
  have hεone : ε < 1 := by linarith
  have hRi : R ≤ δ⁻¹ := by simpa only [one_div] using (le_div_iff₀ hδ).mpr hRδ
  have hci : δ⁻¹ / c ≤ 2 * δ⁻¹ := by
    apply (div_le_iff₀ hc0).mpr
    nlinarith [inv_pos.mpr hδ]
  have hdi : 1 < δ⁻¹ := (one_lt_inv₀ hδ).mpr hδone
  have hei : 100000 * δ⁻¹ < ε⁻¹ := by
    have h := (inv_lt_inv₀ (div_pos hδ (by norm_num : (0 : ℝ) < 100000)) hε).mpr hεsmall
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using h
  linarith

theorem edge_recenter_rescale_budgets {Δ Λ q b s b' s' R D : ℝ}
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hq : 0 < q)
    (hb : 0 < b) (hs : 0 < s) (hb' : 0 < b') (hs' : 0 < s')
    (hsmallb' : b' < 1 / 10000) (hsmalls' : s' < 1 / 10000)
    (hscale : Λ < 1 / (1000000 * Δ))
    (hend : Λ < s' / (100000000 * Δ ^ 2))
    (hbΔ : b' < 1 / (1000000 * Δ))
    (hsb : s < b' / 100000) (hss : s < s' / 100000)
    (hbs : b < s / 100000) (hbb : b < b' / 100000)
    (hclose : |q - 1| ≤ 101 * Δ * Λ)
    (hR : 0 ≤ R) (hRbound : R ≤ 101 * Δ)
    (hD : 0 ≤ D) (hDbound : D < 2 * b) :
    1 / 2 < q⁻¹ ∧ q⁻¹ < 2 ∧
      3 * q⁻¹ * b ≤ b' ∧ R + b'⁻¹ / q⁻¹ + 2 * b ≤ b⁻¹ ∧
      200 * Δ * (1 - q⁻¹) ≤ s' / 100 ∧
      D + s'⁻¹ / q⁻¹ + 2 * s ≤ s⁻¹ ∧
      2 * q⁻¹ * D + 3 * q⁻¹ * s ≤ s' / 2 := by
  have hΔ0 : 0 < Δ := by linarith
  have hscale' : Λ * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hqclose := abs_le.mp hclose
  have hqlow : 99 / 100 < q := by nlinarith
  have hqhigh : q < 101 / 100 := by nlinarith
  have hc0 : 0 < q⁻¹ := inv_pos.mpr hq
  have hclow : 1 / 2 < q⁻¹ := by
    simpa only [one_div] using (show 1 / 2 < 1 / q from (lt_div_iff₀ hq).mpr (by linarith))
  have hchigh : q⁻¹ < 2 := by
    simpa only [one_div] using (show 1 / q < 2 from (div_lt_iff₀ hq).mpr (by linarith))
  have hbudget : 3 * q⁻¹ * b ≤ b' := by nlinarith [mul_lt_mul_of_pos_right hchigh hb]
  have hbΔ' : b' * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hbΔ
  have hRδ : R * b' ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hRbound hb'.le]
  have hdomb := rescale_domain_budget hR hclow hb hb' (by linarith) hbb hRδ
  have hend' : Λ * (100000000 * Δ ^ 2) < s' := (lt_div_iff₀ (by positivity)).mp hend
  have hinv : q * q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  have hcontraction : 1 - q⁻¹ ≤ 2 * 101 * Δ * Λ := by
    have h1 := mul_le_mul_of_nonneg_right hqclose.2 hc0.le
    have h2 := mul_le_mul_of_nonneg_left hchigh.le (by positivity : 0 ≤ 101 * Δ * Λ)
    nlinarith
  have hendbudget : 200 * Δ * (1 - q⁻¹) ≤ s' / 100 := by
    have hh := mul_le_mul_of_nonneg_left hcontraction (by positivity : 0 ≤ 200 * Δ)
    nlinarith
  have hDone : D < 1 := by linarith
  have hDs' : D * s' ≤ 1 := by nlinarith
  have hdoms := rescale_domain_budget hD hclow hs hs' (by linarith) hss hDs'
  have hcD : q⁻¹ * D ≤ 2 * D := mul_le_mul_of_nonneg_right hchigh.le hD
  have hcs : q⁻¹ * s < 2 * s := mul_lt_mul_of_pos_right hchigh hs
  have hfinal : 2 * q⁻¹ * D + 3 * q⁻¹ * s ≤ s' / 2 := by nlinarith
  exact ⟨hclow, hchigh, hbudget, hdomb, hendbudget, hdoms, hfinal⟩

end GC.MetricGeometry
