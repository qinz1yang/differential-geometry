import DifferentialGeometry.Geometry.Comparison.EqualLegAngleDefect
import DifferentialGeometry.Geometry.Metric.Approximation.OppositeLineLifts
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace StrainerRegression

private theorem real_segments (x y : ℝ) : ∃ c : Icc (0 : ℝ) 1 → ℝ,
    c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
    ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by simp, by simp, ?_⟩
  intro s t
  simpa only [Subtype.dist_eq, mul_comm] using dist_lineMap_lineMap x y (s : ℝ) (t : ℝ)

private def lineApprox : KleinerLottApprox (0 : ℝ) (0 : ℝ) (1 / 1000) where
  error_pos := by norm_num
  error_lt_one := by norm_num
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by norm_num
  coverage y hy := by
    have hm : y ∈ id '' ball (0 : ℝ) (1 / 1000)⁻¹ :=
      ⟨y, by change dist y 0 < _; linarith, rfl⟩
    exact (infDist_le_dist_of_mem hm).trans (by norm_num)

theorem flat_straight : 1 + Real.cos (comparisonAngleNegCurvature 0 1 1 2) = 0 := by
  have h := one_add_cos_comparisonAngle_equal_le (κ := 0) (r := 1) (c := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [zero_pow (by decide : 2 ≠ 0), mul_one, sub_self, mul_zero, zero_div] at h
  linarith

theorem hyperbolic_radius_boundary :
    1 + Real.cos (comparisonAngleNegCurvature 1 1 1 (199 / 100)) ≤ 1 / 25 := by
  have h := one_add_cos_comparisonAngle_equal_le (κ := 1) (r := 1) (c := 199 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h.2

theorem zero_radius_and_zero_leg : ∃ a b : ℝ, dist 0 a = 0 ∧ dist 0 b = 0 ∧
    dist a 0 = 0 ∧ dist b 5 = 5 ∧ 0 ≤ -dist a b ∧ -dist a b ≤ 0 := by
  have h := exists_equal_radius_endpoints_with_excess_le real_segments 0 0 5
    (r := 0) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

theorem shifted_line_equal_legs : ∃ (D a b : ℝ), 3 < D ∧ D < 5 ∧
    dist (1 / 2) a = D ∧ dist (1 / 2) b = D ∧
    1 + Real.cos (comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist a b)) < 44 / 3000 := by
  obtain ⟨D, a, b, hDlo, hDhi, ha, hb, he0, he1⟩ :=
    lineApprox.exists_equal_radius_line_lifts real_segments (q := 1 / 2) (r := 4)
      (by norm_num [mem_ball, Real.dist_eq]) (by norm_num)
      (by norm_num [lineApprox, Real.dist_eq])
  have hD3 : 3 < D := by linarith
  have hD5 : D < 5 := by linarith
  have h := (one_add_cos_comparisonAngle_equal_le (κ := 1 / 60)
    (by norm_num) (by linarith : 0 < D) dist_nonneg (by linarith) (by linarith)).2
  have hbudget : 4 * (2 * D - dist a b) / D < 44 / 3000 := by
    apply (div_lt_iff₀ (by linarith : 0 < D)).mpr
    linarith
  exact ⟨D, a, b, hD3, hD5, ha, hb, h.trans_lt hbudget⟩

#print axioms flat_straight
#print axioms hyperbolic_radius_boundary
#print axioms zero_radius_and_zero_leg
#print axioms shifted_line_equal_legs
end StrainerRegression
