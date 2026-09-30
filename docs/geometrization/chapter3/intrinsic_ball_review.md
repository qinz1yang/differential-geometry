# Compiled self-review: intrinsic distance on open balls

Six public theorems and two generated declarations add eight owned declarations.
The192-module gate passes for1025 owned declarations; every new transitive
closure uses only propext, Classical.choice and Quot.sound. Source-copy
unusedArguments, simpNF and synTaut linters are silent; defLemma is unavailable
and kinds were inspected manually. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning is outside these closures. Static
audit passes; no full migrated root, PDF or Overleaf build is claimed.

The driver supplies actual real length curves, proves intrinsic finiteness
for every pair in B(0,10), and uses the local theorem at x=8,h=1/4.
Both endpoints31/4 and33/4 lie on the boundary of the controlled closed
inner ball; the margin is8+4(1/4)=9<10. Their actual intrinsic edistance
and the constructed finite metric distance are both1/2. A separate example
preserves variation of an arbitrary curve under reflection, and the diagonal
case is checked. Initial driver-only noncomputable-definition and extended
real numeral issues were corrected; the script below compiled with exit zero.

Statement audit: paths used for upper bounds lie in the actual ball subtype,
and their variation is proved unchanged on lifting. Finiteness uses actual
center-to-endpoint paths and the already proved intrinsic triangle inequality.
The local equality uses arbitrary positive errors and the exact4h margin;
no compactness, minimizing geodesics, or completeness assumption is hidden.
Topology equivalence and the induced length property remain separate. This
is self-review, not independent human or delegated review.

```lean
import DifferentialGeometry.Topology.MetricSpace.IntrinsicBall
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

private noncomputable def left_inner : ball (0 : ℝ) 10 := ⟨31 / 4, by norm_num [mem_ball, Real.dist_eq]⟩
private noncomputable def right_inner : ball (0 : ℝ) 10 := ⟨33 / 4, by norm_num [mem_ball, Real.dist_eq]⟩

example (a b : ball (0 : ℝ) 10) : intrinsicEDist a b < ⊤ :=
  intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves real_curves 0 (by norm_num) a b

private theorem inner_equality : intrinsicEDist left_inner right_inner = ENNReal.ofReal (1 / 2 : ℝ) := by
  have ht := intrinsicEDist_eq_edist_on_inner_closedBall real_curves
    (x := (8 : ℝ)) (h := 1 / 4) (by norm_num) (by norm_num [Real.dist_eq])
    (a := left_inner) (b := right_inner)
    (by norm_num [left_inner, mem_closedBall, Real.dist_eq])
    (by norm_num [right_inner, mem_closedBall, Real.dist_eq])
  norm_num [left_inner, right_inner, edist_dist, Real.dist_eq] at ht
  exact ht

private theorem ball_finite (a b : ball (0 : ℝ) 10) : intrinsicEDist a b ≠ ⊤ :=
  (intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves real_curves 0 (by norm_num) a b).ne

example : @dist (ball (0 : ℝ) 10) (intrinsicMetricSpace _ ball_finite).toDist
    left_inner right_inner = (1 / 2 : ℝ) := by
  rw [intrinsicMetricSpace_dist, inner_equality]
  norm_num

example (f : unitInterval → ℝ) :
    eVariationOn ((fun x : ℝ => -x) ∘ f) univ = eVariationOn f univ := by
  exact (Isometry.of_dist_eq (fun a b : ℝ => dist_neg_neg a b)).comp_eVariationOn f univ

example : intrinsicEDist left_inner left_inner = 0 := intrinsicEDist_self _

#print axioms eVariationOn.le_of_edist_le
#print axioms Isometry.comp_eVariationOn
#print axioms intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves
#print axioms intrinsicEDist_eq_edist_on_inner_closedBall
```
