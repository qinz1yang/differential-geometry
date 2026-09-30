import DifferentialGeometry.Analysis.Calculus.GraphCoverage
import DifferentialGeometry.Geometry.Metric.RetainedMarkerRadii
import DifferentialGeometry.Analysis.ParameterSelection.AdjustmentBudget
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric GC.MetricGeometry DifferentialGeometry.Analysis

namespace CoverageRegression

theorem original_ball_identity_model :
    hausdorffDist ((univ : Set ℝ) ∩ closedBall 0 1)
      ((fun v : ℝ => (0 : ℝ) + fderiv ℝ id 0 v) '' univ ∩ closedBall 0 1) ≤ 0 := by
  have hh := hausdorffDist_graph_tangent_closedBall_le (id : ℝ → ℝ)
    (ContinuousLinearMap.id ℝ ℝ) (fun z => le_rfl) (fun u => rfl)
    univ 0 (mem_univ _) (R := 1) (B := 0) (e := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => contDiff_id.contDiffAt)
    (by intro u hu; simp [iteratedFDeriv_succ_eq_comp_right])
    (by intro y hy; simp)
    (by intro u hu; exact ⟨u, mem_univ _, by simp⟩)
  simpa only [mul_zero, zero_mul, zero_div, add_zero, ContinuousLinearMap.id_apply] using hh

theorem actual_L2_graph_projection (h : ℝ → ℝ)
    (X : Set (WithLp 2 (ℝ × ℝ))) (x : WithLp 2 (ℝ × ℝ)) (hx : x ∈ X)
    {R B e : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hreg : ∀ u ∈ closedBall x.fst R, ContDiffAt ℝ 2 (fun v => WithLp.toLp 2 (v, h v)) u)
    (hsecond : ∀ u ∈ closedBall x.fst R,
      ‖iteratedFDeriv ℝ 2 (fun v => WithLp.toLp 2 (v, h v)) u‖ ≤ B)
    (hf : ∀ y ∈ X ∩ closedBall x R, dist y (WithLp.toLp 2 (y.fst, h y.fst)) ≤ e)
    (hb : ∀ u ∈ closedBall x.fst R, ∃ y ∈ X, dist y (WithLp.toLp 2 (u, h u)) ≤ e) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + fderiv ℝ (fun u => WithLp.toLp 2 (u, h u)) x.fst v) '' univ ∩
        closedBall x R) ≤ 3 * (2 * e + B * R ^ 2 / 2) := by
  exact hausdorffDist_graph_tangent_closedBall_le _ (WithLp.fstL 2 ℝ ℝ ℝ)
    (fun z => WithLp.norm_fst_le ℝ z) (fun u => rfl) X x hx hR hB he hreg hsecond hf hb

theorem coverage_original_relative_budget {σ Γ r B e : ℝ}
    (hσ : 0 < σ) (hΓ : 0 < Γ) (hB : 0 ≤ B)
    (hr : r ∈ Icc (σ / 2) (2 * σ))
    (he : e ≤ Γ * σ / 24) (hc : B * σ ≤ Γ ^ 3 / 6) :
    3 * (2 * e + B * (r / Γ) ^ 2 / 2) ≤ Γ * r := by
  exact (div_le_iff₀ (by linarith [hr.1] : 0 < r)).mp
    (graph_coverage_relative_error_le hσ hΓ hB hr.1 hr.2 he hc)

private noncomputable def rawScale (p : Bool) : ℝ := if p then 5 / 4 else 3 / 4

theorem unequal_scales_over_same_image :
    ¬ rawScale false = rawScale true ∧
    (3 / 5 : ℝ) * rawScale false ≤ rawScale true ∧
      rawScale true ≤ (5 / 3 : ℝ) * rawScale false := by
  have hh := scale_comparison_of_retained_marker (fun _ : Bool => (0 : ℝ)) rawScale
    (fun _ : Unit => fun _ : ℝ => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
    (by intro i; norm_num)
    (by intro i p hp; cases p <;> norm_num [rawScale])
    (p := false) (q := true) rfl () rfl
  exact ⟨by norm_num [rawScale], hh.2⟩

theorem original_preimages_radius_control :
    |(1 / 2 : ℝ) * rawScale true - (1 / 2 : ℝ) * rawScale false| ≤
      2 * (dist (0 : ℝ) 0 + (1 / 2 : ℝ) * rawScale false) := by
  exact radius_control_of_retained_markers (fun _ : Bool => (0 : ℝ)) rawScale
    (fun _ : Unit => fun _ : ℝ => (1 : ℝ)) (fun _ : Unit => (1 : ℝ))
    (by intro i; norm_num) (fun _ => LipschitzWith.of_dist_le_mul (by intro x y; simp))
    (fun _ => ⟨(), rfl⟩) (by intro i p hp; cases p <;> norm_num [rawScale])
    (by norm_num) (by norm_num) false true

theorem explicit_threshold_at_unit_constants :
    let α := min ((1 : ℝ) / (16 * (1 + 1) * (1 + 1))) (1 / (8 * (1 + 1)))
    0 < α ∧ 16 * α * (1 + 1) * (1 + 1) ≤ 1 ∧ 8 * α * (1 + 1) ≤ 1 := by
  exact adjustment_threshold_pos_and_bounds (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem nonzero_cumulative_adjustment :
    let a := (5 / 3 : ℝ) * (1 / 100) * (1 / 2) + (1 + 1 / 100) * (1 / 100)
    (1 / 100 : ℝ) + a < 1 ∧
      a * 1 * (1 + 1 / 100) + (1 / 100 : ℝ) * (1 + 1 / 100) + 1 / 16 + 2 * (1 / 100) < 1 ∧
      (1 / 100 : ℝ) * (1 + 1 / 100) + 1 / 100 < 1 := by
  exact adjustment_errors_lt_of_threshold (c := 1) (μ := 1) (b := 1) (L := 1)
    (ε := 1 / 100) (σ := 1 / 2) (E := 1 / 100) (H := 1 / 100) (ν := 1 / 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CoverageRegression

namespace CoverageRegression
theorem missing_coordinate_coverage_rejected :
    ¬ (∀ u ∈ closedBall (0 : ℝ) 1, ∃ y ∈ ({0} : Set ℝ), dist y u ≤ 0) := by
  intro h
  obtain ⟨y, hy, hh⟩ := h 1 (by norm_num [mem_closedBall, Real.dist_eq])
  simp only [mem_singleton_iff] at hy
  subst y
  norm_num [Real.dist_eq] at hh
end CoverageRegression

#print axioms CoverageRegression.original_ball_identity_model

#print axioms CoverageRegression.actual_L2_graph_projection

#print axioms CoverageRegression.coverage_original_relative_budget

#print axioms CoverageRegression.unequal_scales_over_same_image

#print axioms CoverageRegression.original_preimages_radius_control

#print axioms CoverageRegression.explicit_threshold_at_unit_constants

#print axioms CoverageRegression.nonzero_cumulative_adjustment

#print axioms CoverageRegression.missing_coordinate_coverage_rejected
