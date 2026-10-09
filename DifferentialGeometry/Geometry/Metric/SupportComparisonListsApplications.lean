import DifferentialGeometry.Geometry.Metric.SupportComparisonLists

/-!
# Consumers of the comparison-list calculus (EGP02, TCP01) on the real line

Constant scale `ρ = 1` (Lipschitz constant zero), `Δ = 1`. An edge support of radius `15` centred at
`30` meets the reference ball `ball 0 20` (the point `16` lies in both); EGP02's list bounds give the
center distance `< 36` and the inclusion of the whole reference ball in `ball 30 57`. A circle support
of radius `10` centred at `15` meets `ball 0 10`; TCP01 gives `ball 0 10 ⊆ ball 15 32`.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

theorem real_line_edge_list_example :
    dist (0 : ℝ) 30 < 36 * 1 * 1 ∧ ball (0 : ℝ) (20 * 1 * 1) ⊆ ball (30 : ℝ) (57 * 1 * 1) := by
  have h := edge_comparison_list_edge_bounds (X := ℝ) (ρ := fun _ => (1 : ℝ)) (Λ := 0)
    (LipschitzWith.const 1) (p := 0) (z := 30) one_pos one_pos le_rfl (by norm_num)
    ⟨16, by rw [mem_closedBall, Real.dist_eq]; norm_num [abs_of_neg],
      by rw [mem_ball, Real.dist_eq]; norm_num⟩
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem real_line_two_stratum_list_example :
    ball (0 : ℝ) (10 * 1) ⊆ ball (15 : ℝ) (32 * 1) :=
  (two_stratum_list_circle_bounds (X := ℝ) (ρ := fun _ => (1 : ℝ)) (Λ := 0)
    (LipschitzWith.const 1) (p := 0) (z := 15) one_pos one_pos le_rfl (by norm_num)
    ⟨6, by rw [mem_closedBall, Real.dist_eq]; norm_num [abs_of_neg],
      by rw [mem_ball, Real.dist_eq]; norm_num⟩).2.2.2

end GC.MetricGeometry
