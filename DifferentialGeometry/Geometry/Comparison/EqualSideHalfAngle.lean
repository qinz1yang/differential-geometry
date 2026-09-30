import DifferentialGeometry.Geometry.Comparison.ModelAngle

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem sinh_half_sq_eq_of_equal_comparison_sides {κ L c : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L) :
    Real.sinh (Real.sqrt κ * c / 2) ^ 2 =
      Real.sinh (Real.sqrt κ * L) ^ 2 *
        (1 - Real.cos (comparisonAngleNegCurvature κ L L c)) / 2 := by
  have hden : Real.sinh (Real.sqrt κ * L) * Real.sinh (Real.sqrt κ * L) ≠ 0 :=
    mul_ne_zero (Real.sinh_pos_iff.mpr (mul_pos (Real.sqrt_pos.mpr hκ) hL)).ne'
      (Real.sinh_pos_iff.mpr (mul_pos (Real.sqrt_pos.mpr hκ) hL)).ne'
  have hcos := cos_comparisonAngleNegCurvature_of_pos hκ hL hL
    (by simpa only [sub_self, abs_zero] using hc) (by linarith : c ≤ L + L)
  have hcosmul := (eq_div_iff hden).mp hcos
  have hdouble := Real.cosh_two_mul (Real.sqrt κ * c / 2)
  rw [show 2 * (Real.sqrt κ * c / 2) = Real.sqrt κ * c by ring] at hdouble
  have hsq := Real.cosh_sq (Real.sqrt κ * L)
  have hhalfsq := Real.cosh_sq (Real.sqrt κ * c / 2)
  nlinarith

theorem cos_half_mul_sinh_le_of_comparison_angle_lower_bound {κ L c σ : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L)
    (hσ : 0 ≤ σ) (hσpi : σ ≤ Real.pi)
    (hangle : Real.pi - σ ≤ comparisonAngleNegCurvature κ L L c) :
    Real.cos (σ / 2) * Real.sinh (Real.sqrt κ * L) ≤
      Real.sinh (Real.sqrt κ * c / 2) := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ Real.pi - σ)
    (comparisonAngleNegCurvature_mem_Icc κ L L c).2 hangle
  rw [Real.cos_pi_sub] at hcos
  have hhalf := Real.cos_two_mul (σ / 2)
  rw [show 2 * (σ / 2) = σ by ring] at hhalf
  have hsquare := sinh_half_sq_eq_of_equal_comparison_sides hκ hL hc hcL
  have hsinh : 0 ≤ Real.sinh (Real.sqrt κ * L) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg (Real.sqrt_nonneg κ) hL.le)
  have hsinhc : 0 ≤ Real.sinh (Real.sqrt κ * c / 2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg (mul_nonneg (Real.sqrt_nonneg κ) hc) (by norm_num))
  have hcoshalf : 0 ≤ Real.cos (σ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  apply (sq_le_sq₀ (mul_nonneg hcoshalf hsinh) hsinhc).mp
  have hmul := mul_le_mul_of_nonneg_left hcos (sq_nonneg (Real.sinh (Real.sqrt κ * L)))
  nlinarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
