# AC20: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The first hit uses only compactness of the parameter interval; no compactness
or completeness of the ambient space is assumed. The proof retains the same
curve and all initial points. Variation bounds its actual remaining endpoint
distance. The angle formulas apply to that same triangle with all denominators
proved positive. The exact nu controls both angle error and distance drop.
Only the initial path must stay inside the ball.

All three fresh leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) pass silently. Six public and one private declaration are
all theorems; defLemma is unavailable in the pinned environment. The combined
gate passes for 75 modules / 2855 jobs / 602 owned constants. All new axiom
closures are standard. The old AreaUpperBarrier warning is outside these
new dependencies. The blueprint static audit passes; no full migrated root
build or new PDF build is claimed. Earlier mathematical leaves are unchanged.

Five compiled examples test zero-radius first hit, a nonmonotone polynomial
curve, positivity of the exact constants at delta=1/100, zero-excess model
angles, and the complete AC20 construction on the real line from its actual
short curves. The example's completeness is used only to construct those
curves; none is assumed by the theorem being tested.

```lean
import DifferentialGeometry.Geometry.Comparison.AlmostRadialPoint
import DifferentialGeometry.Topology.MetricSpace.ApproximateMidpoint

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

example : ∃ s : unitInterval, dist (0 : ℝ) (0 : ℝ) = 0 ∧
    ∀ v : unitInterval, v ≤ s → dist (0 : ℝ) (0 : ℝ) ≤ 0 := by
  exact exists_first_dist_eq_of_continuous_curve (fun _ => (0 : ℝ)) continuous_const
    rfl le_rfl (by simp)

example : ∃ s : unitInterval, dist (0 : ℝ) (6 * (s : ℝ) - 4 * (s : ℝ) ^ 2) = 1 ∧
    ∀ v ≤ s, dist (0 : ℝ) (6 * (v : ℝ) - 4 * (v : ℝ) ^ 2) ≤ 1 := by
  apply exists_first_dist_eq_of_continuous_curve (fun s : unitInterval => 6 * (s : ℝ) - 4 * (s : ℝ) ^ 2)
    (by fun_prop) (by norm_num) (by norm_num) (by norm_num [Real.dist_eq])

example : 0 < min ((1 / 100 : ℝ) ^ 2)
    (min ((1 - cos (1 / 100)) / (sinh (2 + 1) / sinh (2 / 2))) 1) :=
  (almost_radial_constants_pos (a := 2) (A := 2) (δ := 1 / 100)
    (by norm_num) le_rfl (by norm_num) le_rfl).1

example : Real.pi ≤ comparisonAngleNegCurvature 1 1 1 2 ∧
    comparisonAngleNegCurvature 1 2 1 1 ≤ 0 := by
  simpa using comparisonAngles_of_small_triangle_excess (a := 2) (A := 2)
    (r := 2) (t := 1) (s := 1) (η := 0) (δ := 0)
    (by norm_num) le_rfl le_rfl (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by simp)

private theorem real_short_curves (p u : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
      eVariationOn c univ < ENNReal.ofReal (dist p u + η) := by
  have hmid (a b ε : ℝ) (hε : 0 < ε) :
      ∃ z : ℝ, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε := by
    refine ⟨(a + b) / 2, ?_, ?_⟩
    · have heq : a - (a + b) / 2 = (a - b) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div]
      norm_num
      rw [Real.dist_eq a b]
      linarith
    · have heq : b - (a + b) / 2 = (b - a) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div, abs_sub_comm b a]
      norm_num
      rw [Real.dist_eq a b]
      linarith
  obtain ⟨c, hc, hc0, hc1, _, hlen⟩ := exists_curve_eVariationOn_lt_of_approximate_midpoints
    hmid p u hη
  exact ⟨c, hc, hc0, hc1, hlen⟩

example : ∃ y : ℝ, dist 0 y = 1 ∧
    Real.pi - 1 / 100 ≤ comparisonAngleNegCurvature 1 (dist y 2) (dist y 0) (dist (2 : ℝ) 0) ∧
    comparisonAngleNegCurvature 1 (dist (0 : ℝ) 2) (dist 0 y) (dist 2 y) ≤ 1 / 100 := by
  have h := exists_almost_radial_point_with_comparison_angles real_short_curves
    (0 : ℝ) 2 (a := 2) (A := 2) (t := 1) (δ := 1 / 100)
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl
  obtain ⟨y, hy, _, _, hang1, hang2, _⟩ := h
  exact ⟨y, hy, hang1, hang2⟩

#print axioms Metric.exists_first_dist_eq_of_continuous_curve
#print axioms Metric.exists_almost_radial_point_of_curve
#print axioms Metric.exists_almost_radial_point_of_arbitrarily_short_curves
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngles_of_small_triangle_excess
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.almost_radial_constants_pos
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_almost_radial_point_with_comparison_angles
```
