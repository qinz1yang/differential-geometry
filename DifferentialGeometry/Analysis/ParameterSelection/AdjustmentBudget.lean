import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace DifferentialGeometry.Analysis

theorem adjustment_errors_le_of_budget {c μ α b L ε σ E H ν : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hα : 0 ≤ α)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hsmall : ε ≤ 1 / 10) (hεα : ε ≤ α) (hσhalf : σ ≤ 1 / 2)
    (hEα : E ≤ α) (hHα : H ≤ α) (hν : ν ≤ c / 16)
    (hvalue : 16 * α * (1 + b) * (1 + L) ≤ c)
    (hrank : 8 * α * (1 + L) ≤ μ) :
    let a := (5 / 3 : ℝ) * ε * σ + (1 + ε) * E
    E + a ≤ 3 * c / 16 ∧
      a * b * (L + H) + ε * (L + H) + ν + 2 * H ≤ 3 * c / 8 ∧
      ε * (L + H) + H < μ := by
  have hαb := mul_nonneg hα hb
  have hαL := mul_nonneg hα hL
  have hαbL := mul_nonneg hαb hL
  have hαc : 16 * α ≤ c := by nlinarith
  have hαLc : 16 * α * (L + 1) ≤ c := by nlinarith
  have hαbLc : 16 * α * b * (L + 1) ≤ c := by nlinarith
  have hH1 : H ≤ 1 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hσhalf hε
  have hsecond := mul_le_mul_of_nonneg_right hsmall hE
  have ha : (5 / 3 : ℝ) * ε * σ + (1 + ε) * E ≤ 2 * α := by nlinarith
  have hbLH : 0 ≤ b * (L + H) := mul_nonneg hb (add_nonneg hL hH)
  have hab := mul_le_mul_of_nonneg_right ha hbLH
  have haH := mul_le_mul_of_nonneg_left hH1 hαb
  have heH := mul_le_mul_of_nonneg_left hH1 hα
  have heLH := mul_le_mul_of_nonneg_right hεα (add_nonneg hL hH)
  have herr : ((5 / 3 : ℝ) * ε * σ + (1 + ε) * E) * b * (L + H) +
      ε * (L + H) + ν + 2 * H ≤ 3 * c / 8 := by nlinarith
  have hr : ε * (L + H) + H ≤ α * (L + 2) := by nlinarith
  have hquarter : α * (L + 2) ≤ μ / 4 := by nlinarith
  exact ⟨by linarith, herr, by linarith⟩

theorem adjustment_threshold_pos_and_bounds {c μ b L : ℝ}
    (hc : 0 < c) (hμ : 0 < μ) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    let α := min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L)))
    0 < α ∧ 16 * α * (1 + b) * (1 + L) ≤ c ∧ 8 * α * (1 + L) ≤ μ := by
  have hd : 0 < 16 * (1 + b) * (1 + L) := by positivity
  have he : 0 < 8 * (1 + L) := by positivity
  dsimp
  refine ⟨lt_min (div_pos hc hd) (div_pos hμ he), ?_, ?_⟩
  · have hh := (le_div_iff₀ hd).mp
      (min_le_left (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    nlinarith
  · have hh := (le_div_iff₀ he).mp
      (min_le_right (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    nlinarith

theorem adjustment_errors_lt_of_threshold {c μ b L ε σ E H ν : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hsmall : ε ≤ 1 / 10) (hσhalf : σ ≤ 1 / 2) (hν : ν ≤ c / 16)
    (hεα : ε ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hEα : E ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hHα : H ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L)))) :
    let a := (5 / 3 : ℝ) * ε * σ + (1 + ε) * E
    E + a < c ∧ a * b * (L + H) + ε * (L + H) + ν + 2 * H < c ∧
      ε * (L + H) + H < μ := by
  obtain ⟨hα, hv, hr⟩ := adjustment_threshold_pos_and_bounds hc hμ hb hL
  obtain ⟨h1, h2, h3⟩ := adjustment_errors_le_of_budget hc hc1 hμ hα.le
    hb hL hε hE hH hsmall hεα hσhalf hEα hHα hν hv hr
  exact ⟨by linarith, by linarith, h3⟩

end DifferentialGeometry.Analysis
