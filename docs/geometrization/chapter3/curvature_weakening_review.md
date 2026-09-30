# Curvature weakening: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The convexity theorem includes zero. The model-angle theorem keeps positive
adjacent sides, both triangle inequalities, and nonnegative magnitude kappa
for curvature -kappa. It includes both degenerate extremes. The four-point
consumer stays on precisely the supplied subset, with no hidden globalization.
The general parameter result is proved by scaling the unit-curvature
cosine-law inequality. The private helper's axiom closure is also audited.

Both source-copy declaration-linter drivers (`unusedArguments simpNF synTaut`)
and fresh leaf builds pass silently. The pinned environment has no defLemma;
all four owned declarations were checked to be theorems. The combined gate
passes for 67 modules / 2846 jobs / 580 owned constants. It retains the old
AreaUpperBarrier warning, outside the new proof dependencies. No full migrated
root build is claimed. Five compiled probes and three public axiom reports follow.

```lean
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening

open Set
open DifferentialGeometry.Geometry.Comparison.Toponogov

example : ConvexOn ℝ (Ici 0) (fun x => Real.cosh (Real.sqrt x)) :=
  Real.convexOn_cosh_sqrt

example : comparisonAngleNegCurvature 1 3 4 5 ≤ comparisonAngle 3 4 5 :=
  comparisonAngleNegCurvature_le_comparisonAngle (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example {κ a : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) :
    comparisonAngleNegCurvature κ a a 0 ≤ comparisonAngle a a 0 :=
  comparisonAngleNegCurvature_le_comparisonAngle hκ ha ha (by simp) (by linarith)

example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngleNegCurvature 0 a b (a + b) ≤ comparisonAngle a b (a + b) :=
  comparisonAngleNegCurvature_le_comparisonAngle (by norm_num) ha hb
    (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩) le_rfl

example {X : Type*} [MetricSpace X] (p : X) (R : ℝ)
    (h : fourPointComparison 0 (Metric.closedBall p R)) :
    fourPointComparison 1 (Metric.closedBall p R) := h.of_zero (by norm_num)

#print axioms Real.convexOn_cosh_sqrt
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_comparisonAngle
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison.of_zero
```
