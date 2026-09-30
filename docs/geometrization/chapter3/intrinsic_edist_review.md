# Compiled self-review: actual intrinsic extended distance

Fifteen public theorems, three definitions and five generated declarations
add23 owned declarations. The190-module gate passes for1017 owned
declarations; every new transitive closure contains only propext,
Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF and
synTaut linters are silent; defLemma is unavailable and kinds were inspected
manually. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes;
no migrated full-root, PDF or Overleaf build is claimed.

The compiled driver proves the actual length property of the real line via
linear segments, then computes intrinsicEDist(0,2)=2 and the corresponding
finite metric distance=2. On the integers it proves there is no continuous
path from0 to1 using connectedness of a path image in a totally disconnected
space, and obtains intrinsicEDist(0,1)=infinity. The diagonal distance at7
is zero. The actual path t->2t has variation2; concatenating it with its
reverse has variation4. Its constant real-line extension has variation2
on[0,1]. The script below compiled with exit zero.

Statement audit: the infimum ranges over actual continuous paths in the
original topology. Extended distances are retained for inaccessible or
nonrectifiably connected points. Constant paths supply the diagonal case.
Reversal and exact concatenation prove symmetry/triangle without a path
existence assumption. Finite metric conversion requires explicit finiteness
for every pair and exposes its exact distance. No equivalence of the old
and generated topologies or open-ball finiteness is claimed. The finite
length-space specialization uses actual curves/variation. This is self-review,
not independent human or delegated review.

```lean
import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist
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

private theorem real_intrinsic (x y : ℝ) : intrinsicEDist x y = edist x y :=
  intrinsicEDist_eq_edist_of_arbitrarily_short_curves
    (arbitrarily_short_curves_of_metric_segments real_segments) x y

example : intrinsicEDist (0 : ℝ) 2 = 2 := by
  rw [real_intrinsic]
  norm_num [edist_dist, Real.dist_eq]

private theorem real_finite (x y : ℝ) : intrinsicEDist x y ≠ ⊤ := by
  rw [real_intrinsic]
  exact edist_ne_top x y

example : @dist ℝ (intrinsicMetricSpace ℝ real_finite).toDist 0 2 = 2 := by
  rw [intrinsicMetricSpace_dist, real_intrinsic]
  norm_num [edist_dist, Real.dist_eq]

example : intrinsicEDist (0 : ℤ) 1 = ⊤ := by
  apply intrinsicEDist_eq_top_of_not_path
  rintro ⟨γ⟩
  have h := (isPreconnected_range γ.continuous).subsingleton
    (show (0 : ℤ) ∈ range γ from ⟨0, γ.source⟩)
    (show (1 : ℤ) ∈ range γ from ⟨1, γ.target⟩)
  norm_num at h

example : intrinsicEDist (7 : ℤ) 7 = 0 := intrinsicEDist_self 7

private def line02 : Path (0 : ℝ) 2 where
  toFun := fun t => 2 * (t : ℝ)
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

private theorem line02_variation : eVariationOn line02 univ = 2 := by
  have hLip : LipschitzWith 2 line02 := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change |2 * (s : ℝ) - 2 * (t : ℝ)| ≤ 2 * |(s : ℝ) - t|
    rw [← mul_sub, abs_mul]
    norm_num
  apply le_antisymm hLip.eVariationOn_unitInterval_le
  have h := eVariationOn.edist_le line02 (mem_univ (0 : unitInterval)) (mem_univ 1)
  norm_num [line02, edist_dist, Real.dist_eq] at h
  exact h

example : eVariationOn (line02.trans line02.symm) univ = 4 := by
  rw [Path.eVariationOn_trans, Path.eVariationOn_symm, line02_variation]
  norm_num

example : eVariationOn line02.extend (Icc (0 : ℝ) 1) = 2 := by
  rw [Path.eVariationOn_extend, line02_variation]

#print axioms Path.eVariationOn_trans
#print axioms intrinsicEDist_triangle
#print axioms intrinsicEDist_eq_edist_of_arbitrarily_short_curves
#print axioms intrinsicEMetricSpace
#print axioms intrinsicMetricSpace
```
