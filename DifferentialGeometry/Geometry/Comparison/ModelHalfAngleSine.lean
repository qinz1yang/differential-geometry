import DifferentialGeometry.Geometry.Comparison.EqualSideHalfAngle

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem sinh_half_eq_mul_sin_comparison_half {κ L c : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L) :
    Real.sinh (Real.sqrt κ * c / 2) = Real.sinh (Real.sqrt κ * L) *
      Real.sin (comparisonAngleNegCurvature κ L L c / 2) := by
  have hθ := comparisonAngleNegCurvature_mem_Icc κ L L c
  have hs := Real.sin_sq_eq_half_sub (x := comparisonAngleNegCurvature κ L L c / 2)
  rw [show 2 * (comparisonAngleNegCurvature κ L L c / 2) = comparisonAngleNegCurvature κ L L c by ring] at hs
  have hsinh : 0 ≤ Real.sinh (Real.sqrt κ * L) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg (Real.sqrt_nonneg κ) hL.le)
  have hsin : 0 ≤ Real.sin (comparisonAngleNegCurvature κ L L c / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr (by positivity)) (mul_nonneg hsinh hsin)).mp
  rw [mul_pow, hs, sinh_half_sq_eq_of_equal_comparison_sides hκ hL hc hcL]
  ring

theorem sin_half_mul_sinh_le_of_comparison_angle_lower_bound {κ L c θ : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L)
    (hθ : 0 ≤ θ) (hangle : θ ≤ comparisonAngleNegCurvature κ L L c) :
    Real.sin (θ / 2) * Real.sinh (Real.sqrt κ * L) ≤ Real.sinh (Real.sqrt κ * c / 2) := by
  rw [sinh_half_eq_mul_sin_comparison_half hκ hL hc hcL, mul_comm (Real.sin _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sinh_nonneg_iff.mpr (by positivity))
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
    (by linarith [(comparisonAngleNegCurvature_mem_Icc κ L L c).2]) (by linarith)

end DifferentialGeometry.Geometry.Comparison.Toponogov
