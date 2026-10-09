import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.LogCosineBound
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicLogShift
import DifferentialGeometry.Geometry.Comparison.EqualSideHalfAngle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem equal_side_excess_le_log_cos_of_angle_lower_bound {κ L c σ : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hangle : Real.pi - σ ≤ comparisonAngleNegCurvature κ L L c) :
    2 * L - c ≤ -(2 / Real.sqrt κ) * Real.log (Real.cos (σ / 2)) := by
  have hcos : 0 < Real.cos (σ / 2) := by
    have ht : (σ / 2) ^ 2 ≤ 1 := by nlinarith
    linarith [Real.one_sub_sq_div_two_le_cos (x := σ / 2)]
  have hhalf := cos_half_mul_sinh_le_of_comparison_angle_lower_bound hκ hL hc hcL
    hσ (by linarith [Real.two_le_pi]) hangle
  have hshift := Real.add_log_le_of_mul_sinh_le hcos (Real.cos_le_one _) hhalf
  have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  apply (le_of_mul_le_mul_left (a := Real.sqrt κ) · hsqrt)
  have hcancel : Real.sqrt κ * (-(2 / Real.sqrt κ) * Real.log (Real.cos (σ / 2))) =
      -2 * Real.log (Real.cos (σ / 2)) := by field_simp [hsqrt.ne']
  rw [hcancel]
  nlinarith

theorem log_cos_excess_modulus_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ≤ σ ^ (3 / 2 : ℝ) / 2 := by
  have hsqrt : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hlog := Real.neg_log_cos_le_sq_of_abs_le_one
    (show |σ / 2| ≤ 1 by rw [abs_of_nonneg (by positivity)]; linarith)
  have hrpow : σ ^ (3 / 2 : ℝ) = σ * Real.sqrt σ := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hσ, Real.rpow_one]
  rw [hrpow]
  apply (le_of_mul_le_mul_left (a := Real.sqrt σ) · hsqrt)
  have hcancel : Real.sqrt σ * (-(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2))) =
      -2 * Real.log (Real.cos (σ / 2)) := by field_simp [hsqrt.ne']
  rw [hcancel]
  nlinarith [Real.sq_sqrt hσ.le]

theorem equal_side_excess_bound_of_angle_lower_bound {σ L c : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : 0 < L) (hc : 0 ≤ c) (hcL : c ≤ 2 * L)
    (hangle : Real.pi - σ ≤ comparisonAngleNegCurvature σ L L c) :
    0 ≤ 2 * L - c ∧
      2 * L - c ≤ -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ∧
      -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ≤ σ ^ (3 / 2 : ℝ) / 2 :=
  ⟨sub_nonneg.mpr hcL,
    equal_side_excess_le_log_cos_of_angle_lower_bound hσ hL hc hcL hσ.le hσ1 hangle,
    log_cos_excess_modulus_le hσ hσ1⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
