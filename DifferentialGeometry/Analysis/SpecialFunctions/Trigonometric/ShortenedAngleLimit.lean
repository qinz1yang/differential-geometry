import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology

namespace Real

theorem two_arcsin_max_le_of_le_sin_half {θ w : ℝ}
    (hθ : 0 ≤ θ) (hθpi : θ ≤ Real.pi) (hw : w ≤ sin (θ / 2)) :
    2 * arcsin (max 0 w) ≤ θ := by
  have hs : 0 ≤ sin (θ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have ha := arcsin_le_arcsin (max_le hs hw)
  rw [arcsin_sin (by linarith [pi_pos]) (by linarith)] at ha
  linarith

theorem tendsto_shortened_angle_lower_bound {θ B : ℕ → ℝ} {θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) (hθ₀pi : θ₀ ≤ Real.pi)
    (hθ : Tendsto θ atTop (𝓝 θ₀)) (hB : Tendsto B atTop atTop) :
    Tendsto (fun i => 2 * arcsin (max 0 (sin (θ i / 2) -
      ((sin (θ i / 2))⁻¹ - sin (θ i / 2)) / (exp (2 * B i) - 1)))) atTop (𝓝 θ₀) := by
  have hqpos : 0 < sin (θ₀ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hq : Tendsto (fun i => sin (θ i / 2)) atTop (𝓝 (sin (θ₀ / 2))) := by
    simpa only [Function.comp_def] using (continuous_sin.tendsto (θ₀ / 2)).comp (hθ.div_const 2)
  have hExp := tendsto_exp_atTop.comp (hB.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hden : Tendsto (fun i => exp (2 * B i) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hExp
  have herr := ((hq.inv₀ hqpos.ne').sub hq).div_atTop hden
  have hmax := (tendsto_const_nhds (x := (0 : ℝ))).max (hq.sub herr)
  have hh := hmax.arcsin.const_mul 2
  have hvalue : 2 * arcsin (max 0 (sin (θ₀ / 2) - 0)) = θ₀ := by
    rw [sub_zero, max_eq_right hqpos.le,
      arcsin_sin (by linarith [pi_pos]) (by linarith)]
    ring
  rw [hvalue] at hh
  exact hh

end Real
