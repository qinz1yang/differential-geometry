# Compiled self-review: AC13 induced length

Four public theorems in two leaves add four owned declarations. The197-module
build and audit pass for1042 declarations (3031 build jobs); all new transitive
axiom closures contain only propext, Classical.choice and Quot.sound. Source-copy
unusedArguments, simpNF and synTaut linters are silent; declaration kinds
were inspected manually because defLemma is unavailable. Earlier mathematical
leaves remain unchanged. The inherited AreaUpperBarrier warning is outside
these closures. Blueprint static audit passes; no full migrated root, PDF,
Overleaf or human/delegated acceptance is claimed.

The statement audit checks that length is measured in the ACTUAL constructed
intrinsic metric, with its topology and all metric parents supplied explicitly.
The original path topology is used in the defining infimum. Continuity in the
new topology is obtained from the proved topology equality on open balls,
not inferred for arbitrary extended metric spaces. Variation preservation
requires only original continuity and allows infinite length. Subpath clamping
has the correct endpoints even for a zero interval. Arbitrary partition sums
are bounded by the sum of the corresponding subpath variations, which telescopes.
The reverse inequality follows from ambient distance domination. The length
curve is selected from the actual infimum using proved finite intrinsic distance.

Compiled examples below check opposite points -9 and9 of the real open10-ball
with epsilon1/100, and equal endpoints at8. Their continuity, variation and
distance all explicitly use the newly constructed structures. Further checks
cover zero-length subintervals, constant curves, and the infinite-variation
implication without a finiteness hypothesis. These checks do not presume that
the open ball is complete. AC13 is now fully assembled in the explicit
length-curve formulation; ALG06 assembly remains separate.

```lean
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBallLength
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

private def near_left : ball (0 : ℝ) 10 := ⟨-9, by norm_num [mem_ball, Real.dist_eq]⟩
private def near_right : ball (0 : ℝ) 10 := ⟨9, by norm_num [mem_ball, Real.dist_eq]⟩

example : ∃ c : unitInterval → ball (0 : ℝ) 10,
    @Continuous unitInterval (ball (0 : ℝ) 10) inferInstance
      intervalMetric.toUniformSpace.toTopologicalSpace c ∧
    c 0 = near_left ∧ c 1 = near_right ∧
    @eVariationOn unitInterval inferInstance (ball (0 : ℝ) 10)
      intervalMetric.toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace _ intervalMetric.toPseudoEMetricSpace)
      c univ < ENNReal.ofReal (@dist _ intervalMetric.toDist near_left near_right + 1/100) :=
  intrinsicBallMetricSpace_arbitrarily_short_curves real_curves 0 (by norm_num)
    near_left near_right (by norm_num)

example : ∃ c : unitInterval → ball (0 : ℝ) 10,
    @Continuous unitInterval (ball (0 : ℝ) 10) inferInstance
      intervalMetric.toUniformSpace.toTopologicalSpace c ∧
    c 0 = inner_base ∧ c 1 = inner_base ∧
    @eVariationOn unitInterval inferInstance (ball (0 : ℝ) 10)
      intervalMetric.toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace _ intervalMetric.toPseudoEMetricSpace)
      c univ < ENNReal.ofReal (@dist _ intervalMetric.toDist inner_base inner_base + 1/100) :=
  intrinsicBallMetricSpace_arbitrarily_short_curves real_curves 0 (by norm_num)
    inner_base inner_base (by norm_num)

example {X : Type*} [EMetricSpace X] {c : unitInterval → X}
    (hc : Continuous c) (hinfinite : eVariationOn c univ = ⊤) :
    @eVariationOn unitInterval inferInstance X
      (intrinsicEMetricSpace X).toUniformSpace.toTopologicalSpace
      (@PseudoEMetricSpace.toWeakPseudoEMetricSpace X
        (intrinsicEMetricSpace X).toPseudoEMetricSpace) c univ = ⊤ := by
  rw [intrinsicEMetricSpace_eVariationOn hc, hinfinite]

example {X : Type*} [PseudoEMetricSpace X] {c : unitInterval → X}
    (hc : Continuous c) (t : unitInterval) :
    intrinsicEDist (c t) (c t) ≤ eVariationOn c (Icc t t) :=
  intrinsicEDist_le_eVariationOn_Icc hc le_rfl

example : @eVariationOn unitInterval inferInstance ℝ
    (intrinsicEMetricSpace ℝ).toUniformSpace.toTopologicalSpace
    (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℝ
      (intrinsicEMetricSpace ℝ).toPseudoEMetricSpace) (fun _ => (3 : ℝ)) univ = 0 := by
  rw [intrinsicEMetricSpace_eVariationOn continuous_const]
  exact eVariationOn.eq_zero_iff _ |>.mpr (by intro s hs t ht; exact edist_self _)

#print axioms intrinsicEDist_le_eVariationOn_Icc
#print axioms intrinsicEMetricSpace_eVariationOn
#print axioms intrinsicMetricSpace_eVariationOn
#print axioms intrinsicBallMetricSpace_arbitrarily_short_curves
```
