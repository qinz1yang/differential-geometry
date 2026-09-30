# Compiled self-review: actual intrinsic topology and completeness

Nine public theorems, one definition and three generated declarations add13
owned declarations. The195-module gate passes for1038 owned declarations;
new transitive closures contain only propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable and kinds were inspected manually. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside
these closures. Static audit passes; no full migrated root, PDF or Overleaf
build is claimed.

The driver constructs the actual intrinsic metric on the real open10-ball.
It checks topology equality, open embedding and forward nonexpansion, then
completeness of the intrinsic closed balls centered at8 with radii1,0,-1.
At radius1/4, it checks exact equality of the intrinsic-ball image with the
ambient closed ball. Exact constructed distance/edistance formulas are
checked for arbitrary points. All these examples explicitly specify the
constructed metric and generated parent structures. The final script below
compiled silently apart from requested axiom reports.

Statement audit found that a bare local MetricSpace instance on a subtype
could leave the preexisting subtype topology or metric parent selected by
inference. Before acceptance, all affected statements and proof applications
were rewritten with explicit structures. The new completeness theorem uses
the INTRINSIC closed ball and generated uniformity; the topology theorem
compares generated and original topologies. No such inference is left to a
bare local-instance declaration. The metric construction is tied to actual
path infima and proved finiteness; no topology agreement is assumed. This is
self-review, not independent human/delegated review. Induced length remains
separate and no full AC13 claim is made yet.

```lean
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallCompleteness
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic

open Set Metric
open scoped ENNReal

private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments real_segments

@[instance_reducible]
private noncomputable def intervalMetric : MetricSpace (ball (0 : ℝ) 10) :=
  intrinsicBallMetricSpace real_curves 0 (by norm_num)

private def inner_base : ball (0 : ℝ) 10 := ⟨8, by norm_num [mem_ball, Real.dist_eq]⟩

example : intervalMetric.toUniformSpace.toTopologicalSpace =
    (inferInstance : MetricSpace (ball (0 : ℝ) 10)).toUniformSpace.toTopologicalSpace :=
  intrinsicBallMetricSpace_toTopology real_curves 0 (by norm_num)

example : @Topology.IsOpenEmbedding (ball (0 : ℝ) 10) ℝ
    intervalMetric.toUniformSpace.toTopologicalSpace inferInstance Subtype.val :=
  intrinsicBallMetricSpace_isOpenEmbedding real_curves 0 (by norm_num)

example : @LipschitzWith (ball (0 : ℝ) 10) ℝ
    intervalMetric.toPseudoEMetricSpace inferInstance 1 Subtype.val :=
  intrinsicBallMetricSpace_lipschitzWith_coe real_curves 0 (by norm_num)

example : @IsComplete (ball (0 : ℝ) 10) intervalMetric.toUniformSpace
    (@closedBall (ball (0 : ℝ) 10) intervalMetric.toPseudoMetricSpace inner_base 1) :=
  isComplete_intrinsicBall_closedBall real_curves 0 (by norm_num) inner_base
    (by norm_num [inner_base, Real.dist_eq])

example : @IsComplete (ball (0 : ℝ) 10) intervalMetric.toUniformSpace
    (@closedBall (ball (0 : ℝ) 10) intervalMetric.toPseudoMetricSpace inner_base 0) :=
  isComplete_intrinsicBall_closedBall real_curves 0 (by norm_num) inner_base
    (by norm_num [inner_base, Real.dist_eq])

example : @IsComplete (ball (0 : ℝ) 10) intervalMetric.toUniformSpace
    (@closedBall (ball (0 : ℝ) 10) intervalMetric.toPseudoMetricSpace inner_base (-1)) :=
  isComplete_intrinsicBall_closedBall real_curves 0 (by norm_num) inner_base
    (by norm_num [inner_base, Real.dist_eq])

example : (fun y : ball (0 : ℝ) 10 => (y : ℝ)) ''
    (@closedBall (ball (0 : ℝ) 10) intervalMetric.toPseudoMetricSpace inner_base (1 / 4)) =
      closedBall (8 : ℝ) (1 / 4) := by
  exact intrinsicBall_closedBall_image real_curves 0 (by norm_num) inner_base
    (by norm_num) (by norm_num [inner_base, Real.dist_eq])

example (a b : ball (0 : ℝ) 10) : @edist _ intervalMetric.toEDist a b = intrinsicEDist a b :=
  intrinsicBallMetricSpace_edist real_curves 0 (by norm_num) a b

example (a b : ball (0 : ℝ) 10) : @dist _ intervalMetric.toDist a b = (intrinsicEDist a b).toReal :=
  intrinsicBallMetricSpace_dist real_curves 0 (by norm_num) a b

#print axioms PseudoMetricSpace.toTopology_eq_of_locally_dist_eq
#print axioms intrinsicBallMetricSpace
#print axioms intrinsicBallMetricSpace_toTopology
#print axioms intrinsicBallMetricSpace_isOpenEmbedding
#print axioms intrinsicBallMetricSpace_lipschitzWith_coe
#print axioms isComplete_intrinsicBall_closedBall
#print axioms intrinsicBall_closedBall_image
```
