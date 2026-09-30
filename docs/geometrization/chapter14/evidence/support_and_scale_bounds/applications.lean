import DifferentialGeometry.Geometry.Metric.SupportDomainBuffer
import DifferentialGeometry.Geometry.Metric.ZeroSupportIsolation
import DifferentialGeometry.Geometry.Metric.SupportScalePacking
import DifferentialGeometry.Analysis.Calculus.FreezeScale
import DifferentialGeometry.Analysis.Calculus.NormalizedScale
import DifferentialGeometry.Analysis.Integration.Measure.FinitePacking
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

set_option autoImplicit false
open Set Metric MeasureTheory GC.MetricGeometry DifferentialGeometry.Analysis
open scoped ENNReal

namespace SupportScaleRegression

theorem original_two_stratum_domain_margin :
    ∀ x ∈ ball (0 : ℝ) 10, 150 ≤ infDist x (ball (0 : ℝ) 200)ᶜ := by
  have h := support_meeting_ball_buffer (p := (0 : ℝ)) (q := 0)
    (r := 1) (rj := 1) (L := 10) (c := 10) (b := 200)
    (S := {0}) (U := ball 0 200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx; norm_num [mem_singleton_iff.mp hx])
    (by norm_num)
    ⟨0, by simp, by norm_num⟩
  intro x hx
  have hne : (ball (0 : ℝ) 200)ᶜ.Nonempty := ⟨201, by norm_num [mem_ball, Real.dist_eq]⟩
  have hh := h.2.2 x (by simpa using hx) hne
  norm_num at hh
  exact hh

theorem distant_zero_core_covers_original_test_ball :
    dist (900 : ℝ) 0 < 2 * 1000 ∧ ball (0 : ℝ) 1 ⊆ ball 900 1000 := by
  have h := ball_subset_zero_core_of_support_meeting (ρ := fun _ : ℝ => 1)
    (Λ := 0) (LipschitzWith.const 1) (p := 0) (z := 900)
    (by norm_num) (by norm_num) (L := 1) (T := 1000) (R := 1000) (θ := 37 / 40)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by intro _; norm_num)
    ⟨0, by norm_num [mem_closedBall, Real.dist_eq], by norm_num⟩
  simpa using h

theorem actual_meeting_cores_share_enlarged_ball :
    ball (3 : ℝ) 1 ⊆ ball (-3) 40 := by
  have h := enlarged_core_ball_subset_of_supports_meeting (ρ := fun _ : ℝ => 1)
    (Λ := 0) (LipschitzWith.const 1) (p := 0) (z := 3) (w := -3)
    (by norm_num) (by norm_num) (by norm_num) (R := 5) (C := 2) (a := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨3, by norm_num, by norm_num [mem_ball, Real.dist_eq]⟩
    ⟨-3, by norm_num, by norm_num [mem_ball, Real.dist_eq]⟩
  norm_num at h
  exact h

theorem saturated_three_core_measure_bound : ((Finset.univ : Finset (Fin 3)).card : ℝ) ≤ 3 := by
  let : MeasurableSpace (Fin 3) := ⊤
  change ((Finset.univ : Finset (Fin 3)).card : ℝ) ≤ 3
  apply card_le_of_disjoint_measure_comparison (μ := Measure.count) (I := Finset.univ) (b := 3)
    (U := fun i : Fin 3 => {i}) (V := fun _ => univ) (by norm_num)
  · intro i _ j _ hij
    exact disjoint_singleton.mpr hij
  · intro i _; exact MeasurableSet.singleton i
  · intro i _; simp [Measure.real]
  · intro i _; simp [Measure.count_univ]
  · intro i _ j _; exact subset_univ _
  · intro i _; norm_num [Measure.real, Measure.count_univ]

private noncomputable def slope : ℝ →L[ℝ] ℝ := (1 / 100 : ℝ) • ContinuousLinearMap.id ℝ ℝ
private noncomputable def scale (x : ℝ) := slope x + 1

private theorem scale_derivative (x : ℝ) :
    DifferentiableAt ℝ scale x ∧ ‖fderiv ℝ scale x‖ ≤ 1 / 100 := by
  have h := (slope.hasFDerivAt (x := x)).add_const 1
  refine ⟨h.differentiableAt, ?_⟩
  change ‖fderiv ℝ (fun y => slope y + 1) x‖ ≤ _
  rw [h.fderiv]
  norm_num [slope, norm_smul, ContinuousLinearMap.norm_id]

theorem actual_nonconstant_scale_product_bound :
    max |scale 1 * 1 - 1|
      ‖fderiv ℝ (fun x => scale x * x) 1 - fderiv ℝ (fun x : ℝ => x) 1‖ ≤ 3 / 100 := by
  have h := freeze_scale_product_c1_le (scale_derivative 1).1
    (show DifferentiableAt ℝ (fun x : ℝ => x) 1 from differentiableAt_id) (L := 1) (Λ := 1 / 100) (V := 1 / 2) (Δ := 2) (A := 1)
    (by norm_num [scale, slope]) (scale_derivative 1).2
    (by norm_num) (by simp)
  simpa only [id_eq, smul_eq_mul, Real.norm_eq_abs] using h.trans_eq (by norm_num)

theorem actual_nonconstant_scale_quotient_bound :
    max |1 / scale 1 - 1|
      ‖fderiv ℝ (fun x => x / scale x) 1 - fderiv ℝ (fun x : ℝ => x) 1‖ ≤ 2 / 25 := by
  have h := freeze_scale_quotient_c1_le (scale_derivative 1).1
    (show DifferentiableAt ℝ (fun x : ℝ => x) 1 from differentiableAt_id) (L := 1) (Λ := 1 / 100) (C := 1 / 2) (Δ := 2) (D₁ := 1)
    (by norm_num) (by norm_num [scale, slope]) (scale_derivative 1).2
    (by norm_num) (by simp)
  exact h.trans_eq (by norm_num)

theorem actual_affine_scale_bounds_on_closed_ball :
    ∀ x ∈ closedBall (0 : ℝ) 10,
      |(2 + (2 * x) / 100) / 2 - 1| ≤ 1 / 10 ∧
      ‖fderiv ℝ (fun y : ℝ => (2 + (2 * y) / 100) / 2) x‖ ≤ 1 / 100 ∧
      (2 + (2 * x) / 100) / 2 ∈ Icc (1 / 2) (3 / 2) := by
  have hlip : LipschitzWith (1 / 100 : NNReal) (fun x : ℝ => 2 + x / 100) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, add_sub_add_left_eq_sub, ← sub_div, abs_div]
    norm_num
    exact le_of_eq (by ring)
  have h := normalized_scale_in_affine_coordinates hlip (0 : ℝ) (by norm_num)
    (L := 10) (by norm_num)
  norm_num at h ⊢
  exact h.2

end SupportScaleRegression
