import DifferentialGeometry.Analysis.Calculus.Taylor.QuadraticBound

/-!
# One-variable tangent and chord estimates (BCP02.c and BCP03.a kernels)

Blueprint 207B, BCP02 (`B:8212`, display BCP02.c) and BCP03 (`B:8323`, display BCP03.a). Along a
curve, a scalar function with second derivative bounded by `c` satisfies
* the chord test `|f'(x) - (f(x + ℓ) - f(x))/ℓ| ≤ c ℓ / 2` (BCP02.c with `c = 2r`);
* the oscillation test: if `f` is defined on the whole line with oscillation at most `ε`, then
  `f'(x)² ≤ 2 c ε` (BCP03.a with `c = 10`: `‖dF‖² ≤ 20 osc F`; the blueprint follows the complete
  geodesic for time `b/10`, which may pass through loops).
Both are consequences of the tree's quadratic Taylor bound
`norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem fderiv_apply_eq_mul_deriv (f : ℝ → ℝ) (x h : ℝ) :
    (fderiv ℝ f x) h = h * deriv f x := by
  have hsmul := (fderiv ℝ f x).map_smul h (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hsmul
  rw [hsmul]
  rfl

/-- The quadratic Taylor bound in one variable, forward segment form. -/
theorem abs_sub_sub_mul_deriv_le {f : ℝ → ℝ} {c x ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hf : ∀ t ∈ Icc x (x + ℓ), ContDiffAt ℝ 2 f t)
    (hM : ∀ t ∈ Icc x (x + ℓ), ‖iteratedFDeriv ℝ 2 f t‖ ≤ c) :
    |f (x + ℓ) - f x - ℓ * deriv f x| ≤ c / 2 * ℓ ^ 2 := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (x + ℓ - x) ∈ Icc x (x + ℓ) := by
    intro t ht
    simp only [add_sub_cancel_left, smul_eq_mul]
    constructor <;> nlinarith [ht.1, ht.2]
  have h := norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le (f := f) (q := x) (y := x + ℓ)
    (fun t ht => hf _ (hseg t ht)) (fun t ht => hM _ (hseg t ht))
  simpa only [add_sub_cancel_left, Real.norm_eq_abs, fderiv_apply_eq_mul_deriv, sq_abs] using h

/-- BCP02.c: the chord test of an adapted coordinate along a segment of length `ℓ`. -/
theorem abs_deriv_sub_chord_le {f : ℝ → ℝ} {c x ℓ : ℝ} (hℓ : 0 < ℓ)
    (hf : ∀ t ∈ Icc x (x + ℓ), ContDiffAt ℝ 2 f t)
    (hM : ∀ t ∈ Icc x (x + ℓ), ‖iteratedFDeriv ℝ 2 f t‖ ≤ c) :
    |deriv f x - (f (x + ℓ) - f x) / ℓ| ≤ c / 2 * ℓ := by
  have h := abs_sub_sub_mul_deriv_le hℓ.le hf hM
  have he : deriv f x - (f (x + ℓ) - f x) / ℓ = -(f (x + ℓ) - f x - ℓ * deriv f x) / ℓ := by
    field_simp
    ring
  rw [he, abs_div, abs_neg, abs_of_pos hℓ, div_le_iff₀ hℓ]
  linarith [show c / 2 * ℓ * ℓ = c / 2 * ℓ ^ 2 by ring]

/-- BCP03.a: a function on the line with second derivative bounded by `c > 0` and oscillation at
most `ε` has `f'(x)² ≤ 2 c ε` everywhere. -/
theorem sq_deriv_le_of_oscillation {f : ℝ → ℝ} {c ε : ℝ} (hc : 0 < c) (hf : ContDiff ℝ 2 f)
    (hM : ∀ t, ‖iteratedFDeriv ℝ 2 f t‖ ≤ c) (hosc : ∀ s t, f t - f s ≤ ε) (x : ℝ) :
    deriv f x ^ 2 ≤ 2 * c * ε := by
  set b := deriv f x with hb
  have h := norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le (f := f) (q := x) (y := x + b / c)
    (fun t _ => hf.contDiffAt) (fun t _ => hM _)
  simp only [add_sub_cancel_left, Real.norm_eq_abs, fderiv_apply_eq_mul_deriv, sq_abs] at h
  rw [← hb] at h
  have hlow := (abs_le.mp h).1
  have hup := hosc x (x + b / c)
  have hq : b / c * b - c / 2 * (b / c) ^ 2 = b ^ 2 / (2 * c) := by
    field_simp
    ring
  have h2 : b ^ 2 / (2 * c) ≤ ε := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at h2

end DifferentialGeometry.Analysis
