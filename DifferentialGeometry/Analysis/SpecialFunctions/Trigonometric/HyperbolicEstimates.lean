import DifferentialGeometry.Analysis.Convex.Hyperbolic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

open Set

namespace Real

theorem cosh_sub_one_le_sq {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    cosh t - 1 ≤ t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have h := convexOn_cosh_sqrt.2 (show (0 : ℝ) ∈ Ici 0 by simp)
    (show (1 : ℝ) ∈ Ici 0 by simp) (sub_nonneg.mpr ht2) (sq_nonneg t)
    (show (1 - t ^ 2) + t ^ 2 = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, sqrt_sq ht, sqrt_zero,
    sqrt_one, cosh_zero] at h
  have he : exp (-1 : ℝ) ≤ 1 := by simp
  have hc : cosh 1 ≤ 2 := by rw [cosh_eq]; linarith [exp_one_lt_three]
  nlinarith

theorem sinh_sub_self_le_sq {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |sinh t - t| ≤ t ^ 2 := by
  have hder (x : ℝ) : HasDerivAt (fun x : ℝ => sinh x - x) (cosh x - 1) x :=
    (hasDerivAt_sinh x).sub (hasDerivAt_id x)
  have hb (x : ℝ) (hx : x ∈ Icc 0 t) : ‖cosh x - 1‖ ≤ t := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (one_le_cosh x))]
    have h := cosh_sub_one_le_sq hx.1 (hx.2.trans ht1)
    nlinarith [hx.1, hx.2, mul_nonneg hx.1 (show 0 ≤ 1 - x by linarith [hx.2])]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hder x).hasDerivWithinAt) hb (convex_Icc 0 t)
    (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  simpa [Real.norm_eq_abs, abs_of_nonneg ht, pow_two] using h

theorem abs_cosh_sub_linear_le {r c t R : ℝ}
    (hr : 0 ≤ r - t) (hR : r + t ≤ R) (hc : |c - r| ≤ t) :
    |cosh c - cosh r - (c - r) * sinh r| ≤ cosh R * t ^ 2 := by
  have ht : 0 ≤ t := (abs_nonneg _).trans hc
  have hr0 : 0 ≤ r := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hmemr : r ∈ Icc (r - t) (r + t) := by constructor <;> linarith
  have hmemc : c ∈ Icc (r - t) (r + t) := by
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    constructor <;> linarith
  have hbound (x : ℝ) (hx : x ∈ Icc (r - t) (r + t)) : ‖cosh x‖ ≤ cosh R := by
    rw [norm_eq_abs, abs_of_pos (cosh_pos x)]
    exact cosh_le_cosh.mpr (by rw [abs_of_nonneg (hr.trans hx.1), abs_of_nonneg hR0]; linarith [hx.2])
  have hsinh (x : ℝ) (hx : x ∈ Icc (r - t) (r + t)) : |sinh x - sinh r| ≤ cosh R * t := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hasDerivAt_sinh x).hasDerivWithinAt) hbound
      (convex_Icc _ _) hmemr hx
    rw [norm_eq_abs, norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) (cosh_pos R).le)
  have hder (x : ℝ) : HasDerivAt (fun x : ℝ => cosh x - cosh r - (x - r) * sinh r)
      (sinh x - sinh r) x := by
    convert ((hasDerivAt_cosh x).sub_const (cosh r)).sub
      (((hasDerivAt_id x).sub_const r).mul_const (sinh r)) using 1 <;> simp
    rfl
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hder x).hasDerivWithinAt) (fun x hx => by simpa only [norm_eq_abs] using hsinh x hx)
    (convex_Icc _ _) hmemr hmemc
  simp only [sub_self, zero_mul, sub_zero, norm_eq_abs] at h
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg (cosh_pos R).le ht)])

end Real
