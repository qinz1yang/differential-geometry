import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Real

theorem convexOn_sinh_nonneg : ConvexOn ℝ (Ici 0) sinh := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply hasSum_le _ (hasSum_sinh (a * x + b * y)) (((hasSum_sinh x).mul_left a).add ((hasSum_sinh y).mul_left b))
  intro n
  have hpow := (convexOn_pow (2 * n + 1) (𝕜 := ℝ)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hpow
  have hdiv := div_le_div_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ (2 * n + 1).factorial)
  simpa [add_div, mul_div_assoc] using hdiv

theorem sinh_mul_le_mul_sinh {t h : ℝ} (ht : t ∈ Icc 0 1) (hh : 0 ≤ h) :
    sinh (t * h) ≤ t * sinh h := by
  have hc := convexOn_sinh_nonneg.2 (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp) hh
    (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (show 1 - t + t = 1 by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add, sinh_zero] using hc

theorem sinh_le_mul_sinh_div {h D : ℝ} (hh : 0 ≤ h) (hD : 0 < D) (hhD : h ≤ D) :
    sinh h ≤ h * (sinh D / D) := by
  have ht : h / D ∈ Icc 0 1 := ⟨div_nonneg hh hD.le, (div_le_one hD).mpr hhD⟩
  have hc := sinh_mul_le_mul_sinh ht hD.le
  rw [div_mul_cancel₀ _ hD.ne'] at hc
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hc

theorem mul_sinh_le_sinh_mul_of_le {t h D : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hD : 0 < D) (hhD : h ≤ D) :
    (t * D / sinh D) * sinh h ≤ sinh (t * h) := by
  have hsD : 0 < sinh D := sinh_pos_iff.mpr hD
  have hc := sinh_le_mul_sinh_div hh hD hhD
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ t * D / sinh D by positivity)
  have heq : (t * D / sinh D) * (h * (sinh D / D)) = t * h := by
    field_simp
  rw [heq] at hm
  exact hm.trans (self_le_sinh_iff.mpr (mul_nonneg ht hh))

end Real
