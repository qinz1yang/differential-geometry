import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Real

theorem convexOn_cosh_sqrt : ConvexOn ℝ (Ici 0) (fun x => cosh (sqrt x)) := by
  have hs (x : ℝ) (hx : 0 ≤ x) :
      HasSum (fun n : ℕ => x ^ n / ((2 * n).factorial : ℝ)) (cosh (sqrt x)) := by
    convert hasSum_cosh (sqrt x) using 1
    ext n
    rw [pow_mul, sq_sqrt hx]
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hxy : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  apply hasSum_le _ (hs (a * x + b * y) hxy) (((hs x hx).mul_left a).add ((hs y hy).mul_left b))
  intro n
  have hpow := (convexOn_pow n (𝕜 := ℝ)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hpow
  have hdiv := div_le_div_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ (2 * n).factorial)
  simpa [add_div, mul_div_assoc] using hdiv

end Real
