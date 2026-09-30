import DifferentialGeometry.Geometry.Metric.RadialSupportBuffer
import DifferentialGeometry.Geometry.Metric.WeakEdgeLocalization
import Mathlib.Tactic

set_option autoImplicit false
open Set Metric GC.MetricGeometry

namespace LocalizationRegression

theorem large_zero_radius_retains_original_shell :
    (1600 : ℝ) / 20 ≤ 2000 ∧
      ∀ x ∈ ball (0 : ℝ) 1, dist 1000 x / 2000 ∈ Icc (3 / 20) (19 / 20) := by
  have h := radial_support_test_ball_buffer (ρ := fun _ : ℝ => 1)
    (η := fun x => dist 1000 x / 2000) (Λ := 0) (LipschitzWith.const 1)
    (p := 0) (z := 1000) (by norm_num) (by norm_num)
    (L := 1) (T := 1600) (R := 2000) (e := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro _; norm_num) (S := {0}) (by intros; norm_num)
    (by intro x hx; norm_num [mem_singleton_iff.mp hx, Real.dist_eq])
    ⟨0, by simp, by norm_num⟩
  simpa only [mul_one, div_one] using h

private theorem numerator_lipschitz : LipschitzWith 1 (fun x : ℝ => 100 + |x|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, add_sub_add_left_eq_sub] using
    abs_abs_sub_abs_le_abs_sub x y

theorem actual_nonsmooth_numerator_has_both_domain_bounds :
    ∀ x ∈ ball (0 : ℝ) 1,
      100 + |x| ∈ Icc 12 1086 ∧ dist x 0 < 6000 := by
  have h := weak_edge_quotient_alternative numerator_lipschitz
    (ρ := fun _ : ℝ => 1) (Λ := 0) (LipschitzWith.const 1) (by norm_num)
    (fun x => by positivity) (fun _ => by norm_num)
    (p := 0) (q := 0) (L := 1) (Δ := 120)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (E := {0}) (by norm_num)
  rcases h with hlo | ⟨_, hhi⟩
  · have hf := hlo 0 (by norm_num)
    norm_num at hf
  · intro x hx
    have hh := hhi x (by simpa using hx)
    norm_num only [mul_one, div_one, infDist_singleton] at hh
    norm_num at hh
    simpa only [mem_Icc, Real.dist_eq, sub_zero] using hh

theorem original_support_center_supplies_strong_edge_proximity :
    (1 : ℝ) < 63 / 50 ∧ infDist (0 : ℝ) ({2300} : Set ℝ) < 3600 := by
  have h := strong_set_proximity_of_support_meeting (ρ := fun _ : ℝ => 1)
    (Λ := 0) (LipschitzWith.const 1) (p := 0) (z := 2300)
    (by norm_num) (by norm_num) (L := 1) (Δ := 120)
    (by norm_num) (by norm_num) (by norm_num) (E := {2300}) (by simp)
    ⟨0, by norm_num [mem_closedBall, Real.dist_eq], by norm_num⟩
  convert h using 1 <;> norm_num

end LocalizationRegression
