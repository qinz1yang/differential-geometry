# AC19: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The main theorem retains the exact blueprint constant, positive side
conditions and both closed triangle inequalities. The metric consumer
proves those inequalities rather than asking for a model triangle unrelated
to its points. Curvature magnitude one means actual curvature minus one.
The direct mean-value proof uses a weaker intermediate linear remainder;
its total estimate still fits the advertised constant. No stronger
intermediate Taylor bound is claimed.

Both fresh leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) compile silently. All five source declarations are theorems;
defLemma is unavailable in the pinned environment. The combined gate passes
for 72 modules / 2852 jobs / 595 owned constants. All new transitive axiom
closures are standard. The inherited AreaUpperBarrier warning is outside
the new dependencies. No full migrated root build is claimed.

Six compiled examples cover the zero small-argument endpoint, the maximum
small-argument endpoint, both degenerate triangle extremes, a nondegenerate
triangle, and an actual metric-triangle application. The degenerate probes
also use t=1=a/2, so both short-side upper bounds are attained.

```lean
import DifferentialGeometry.Geometry.Comparison.ModelAngleFiniteDifference

open Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

example : cosh (0 : ℝ) - 1 ≤ (0 : ℝ) ^ 2 := cosh_sub_one_le_sq le_rfl (by norm_num)

example : |sinh (1 : ℝ) - 1| ≤ (1 : ℝ) ^ 2 := sinh_sub_self_le_sq (by norm_num) le_rfl

example : |(1 : ℝ) - 2 + cos (comparisonAngleNegCurvature 1 2 1 1)| ≤
    4 * cosh 3 / sinh 2 := by
  simpa [show (2 : ℝ) + 1 = 3 by norm_num] using abs_sub_add_cos_comparisonAngleNegCurvature_one_le
    (a := 2) (A := 2) (r := 2) (t := 1) (c := 1)
    (by norm_num) le_rfl le_rfl (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num)

example : |(3 : ℝ) - 2 + cos (comparisonAngleNegCurvature 1 2 1 3)| ≤
    4 * cosh 3 / sinh 2 := by
  simpa [show (2 : ℝ) + 1 = 3 by norm_num] using abs_sub_add_cos_comparisonAngleNegCurvature_one_le
    (a := 2) (A := 2) (r := 2) (t := 1) (c := 3)
    (by norm_num) le_rfl le_rfl (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num)

example : |cos (comparisonAngleNegCurvature 1 2 1 2)| ≤ 4 * cosh 3 / sinh 2 := by
  simpa [show (2 : ℝ) + 1 = 3 by norm_num] using abs_sub_add_cos_comparisonAngleNegCurvature_one_le
    (a := 2) (A := 2) (r := 2) (t := 1) (c := 2)
    (by norm_num) le_rfl le_rfl (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num)

example : |dist (1 : ℝ) 2 - dist (0 : ℝ) 2 + dist (0 : ℝ) 1 *
    cos (comparisonAngleNegCurvature 1 (dist (0 : ℝ) 2) (dist (0 : ℝ) 1) (dist (1 : ℝ) 2))| ≤
    (4 * cosh (2 + 1) / sinh 2) * (dist (0 : ℝ) 1) ^ 2 := by
  apply abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le (0 : ℝ) 1 2
    (a := 2) (A := 2) <;> norm_num [Real.dist_eq]

#print axioms Real.cosh_sub_one_le_sq
#print axioms Real.sinh_sub_self_le_sq
#print axioms Real.abs_cosh_sub_linear_le
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.abs_sub_add_cos_comparisonAngleNegCurvature_one_le
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le
```
