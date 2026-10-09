import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicSlope
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.AngleEstimates
import DifferentialGeometry.Topology.MetricSpace.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

open Set Real Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem pi_sub_lt_comparisonAngleNegCurvature_of_balanced_excess
    {L s ν τ : ℝ} (hL : 0 < L) (hL1 : L ≤ 1) (hν : 0 < ν) (hνhalf : ν ≤ 1 / 2)
    (hτ : 0 < τ) (hLs : L / 2 ≤ s) (hs : s < (1 + ν) * L / 2)
    (hbudget : 8 * cosh 2 * ν ≤ 1 - cos τ) :
    Real.pi - τ < comparisonAngleNegCurvature 1 s s L := by
  have hs0 : 0 < s := by linarith
  have h2s : 2 * s ≤ 2 * L := by nlinarith
  have hsinhs : 0 < sinh s := sinh_pos_iff.mpr hs0
  have hden : 0 < sinh s * sinh s := mul_pos hsinhs hsinhs
  have hscale : sinh (2 * s) ≤ 2 * L * cosh 2 := by
    have hh := sinh_le_self_mul_cosh (show 0 ≤ 2 * s by positivity) (show 2 * s ≤ 2 by linarith)
    exact hh.trans (mul_le_mul_of_nonneg_right h2s (cosh_pos 2).le)
  have hnum : cosh (2 * s) - cosh L < 2 * L * cosh 2 * (ν * L) := by
    have h := cosh_sub_le_sinh_mul_sub hL.le (show L ≤ 2 * s by linarith) le_rfl
    have h' := mul_le_mul_of_nonneg_right hscale (show 0 ≤ 2 * s - L by linarith)
    exact (h.trans h').trans_lt
      (mul_lt_mul_of_pos_left (show 2 * s - L < ν * L by nlinarith)
        (mul_pos (by positivity) (cosh_pos 2)))
  have hdenlo : L ^ 2 / 4 ≤ sinh s * sinh s := by
    have ht := self_le_sinh_iff.mpr hs0.le
    have hb : L / 2 ≤ sinh s := hLs.trans ht
    nlinarith [sq_nonneg (sinh s - L / 2)]
  have hcos : cos (comparisonAngleNegCurvature 1 s s L) =
      (cosh s * cosh s - cosh L) / (sinh s * sinh s) := by
    simpa using cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1)
      hs0 hs0 (by simpa using hL.le) (by linarith)
  have hlaw := (eq_div_iff hden.ne').mp hcos
  have hdouble : cosh (2 * s) = cosh s * cosh s + sinh s * sinh s := by
    rw [two_mul, cosh_add]
  have hcosbound : 1 + cos (comparisonAngleNegCurvature 1 s s L) < 8 * cosh 2 * ν := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    have h := mul_le_mul_of_nonneg_left hdenlo (show 0 ≤ 8 * cosh 2 * ν by positivity)
    nlinarith only [hlaw, hnum, h, hdouble]
  by_contra h
  have hc := cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngleNegCurvature_mem_Icc 1 s s L).1
    (show Real.pi - τ ≤ Real.pi by linarith) (le_of_not_gt h)
  rw [cos_pi_sub] at hc
  linarith

theorem exists_balanced_midpoint_with_comparison_angle
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (x y : X) {τ : ℝ} (hL : 0 < dist x y) (hL1 : dist x y ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    let ν := min (1 / 2) ((1 - cos τ) / (8 * cosh 2))
    0 < ν ∧ ∃ z : X, dist x z = dist y z ∧
      dist x y / 2 ≤ dist x z ∧ dist x z < (1 + ν) * dist x y / 2 ∧
      (1 + ν) * dist x y / 2 ≤ 3 * dist x y / 4 ∧
      Real.pi - τ < comparisonAngleNegCurvature 1 (dist z x) (dist z y) (dist x y) := by
  let ν := min (1 / 2) ((1 - cos τ) / (8 * cosh 2))
  have hcos : 0 < 1 - cos τ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      (show τ ≤ Real.pi by linarith [two_le_pi]) hτ
    rw [cos_zero] at h
    linarith
  have hden : 0 < 8 * cosh (2 : ℝ) := by positivity
  have hν : 0 < ν := lt_min (by norm_num) (div_pos hcos hden)
  have hνhalf : ν ≤ 1 / 2 := min_le_left _ _
  have hbudget : 8 * cosh 2 * ν ≤ 1 - cos τ := by
    have h := (le_div_iff₀ hden).mp (min_le_right (1 / 2) ((1 - cos τ) / (8 * cosh 2)))
    nlinarith
  obtain ⟨z, heq, hlo, hup⟩ := exists_balanced_midpoint_of_arbitrarily_short_curves hcurves x y hν hL
  refine ⟨hν, z, heq, hlo, hup, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hνhalf hL.le]
  · rw [dist_comm z x, dist_comm z y, ← heq]
    exact pi_sub_lt_comparisonAngleNegCurvature_of_balanced_excess hL hL1 hν hνhalf hτ hlo hup hbudget

end DifferentialGeometry.Geometry.Comparison.Toponogov
