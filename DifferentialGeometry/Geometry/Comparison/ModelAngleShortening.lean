import DifferentialGeometry.Geometry.Comparison.ModelHalfAngleSine
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicShiftRatio

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem sin_half_comparison_angle_lower_bound_of_shortening {κ L r c d θ : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hrL : r ≤ L)
    (hc : 0 ≤ c) (hcL : c ≤ 2 * L) (hd : 0 ≤ d) (hdr : d ≤ 2 * r)
    (htail : c - 2 * (L - r) ≤ d) (hθ : 0 < θ)
    (hangle : θ ≤ comparisonAngleNegCurvature κ L L c) :
    Real.sin (θ / 2) - ((Real.sin (θ / 2))⁻¹ - Real.sin (θ / 2)) /
      (Real.exp (2 * (Real.sqrt κ * r)) - 1) ≤
      Real.sin (comparisonAngleNegCurvature κ r r d / 2) := by
  have hL : 0 < L := hr.trans_le hrL
  have hθpi : θ ≤ Real.pi := hangle.trans (comparisonAngleNegCurvature_mem_Icc κ L L c).2
  have hq : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hhalf := sin_half_mul_sinh_le_of_comparison_angle_lower_bound hκ hL hc hcL hθ.le hangle
  have hshift := Real.add_log_le_of_mul_sinh_le hq (Real.sin_le_one _) hhalf
  have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hshort : Real.sqrt κ * r + Real.log (Real.sin (θ / 2)) ≤ Real.sqrt κ * d / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htail hsqrt.le]
  have hB : 0 < Real.sqrt κ * r := mul_pos hsqrt hr
  have hsinh := Real.sinh_le_sinh.mpr hshort
  rw [sinh_half_eq_mul_sin_comparison_half hκ hr hd hdr] at hsinh
  rw [← Real.sinh_add_log_div_sinh hB hq]
  apply (div_le_iff₀ (Real.sinh_pos_iff.mpr hB)).mpr
  simpa only [mul_comm] using hsinh

end DifferentialGeometry.Geometry.Comparison.Toponogov
