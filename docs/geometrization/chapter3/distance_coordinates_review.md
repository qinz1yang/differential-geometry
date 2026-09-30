# Distance coordinates and AC15: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The map uses actual ambient distances and Mathlib's PiLp targets. The exact
l1 and l2 constants include the empty index set. The image-dimension theorem
requires real interior or a positive-radius ball, and bounds the actual
source subset's Hausdorff dimension. No injectivity conclusion is inferred.
The target dimension uses the canonical WithLp linear equivalence.

Both fresh leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) pass silently. Eight theorems and one noncomputable definition
are inspected; defLemma is unavailable in this environment. The combined
gate passes for 79 modules / 2867 jobs / 616 owned constants. All new axiom
closures are standard. The inherited AreaUpperBarrier warning is outside
the new dependencies; no full migrated root is built. Earlier mathematical
leaves and blueprint207 are unchanged.

Six compiled examples cover empty coordinates, two Euclidean coordinates,
the infinity norm, a concrete distance-coordinate value, the generic open
image theorem on the real line, and a genuine one-coordinate distance map
whose interval image contains a positive-radius l1 ball. That last consumer
constructs the preimage from its actual coordinate rather than assuming an
image-interior proposition.

```lean
import DifferentialGeometry.Topology.MetricSpace.DistanceCoordinates
import Mathlib.Tactic

open Set Metric
open scoped ENNReal NNReal

example (a : Fin 0 → ℝ) : LipschitzWith 0 (distanceCoordinates 1 a) := by
  simpa using lipschitzWith_distanceCoordinates_one a

example (a : Fin 2 → ℝ) : LipschitzWith (NNReal.sqrt 2) (distanceCoordinates 2 a) := by
  simpa using lipschitzWith_distanceCoordinates_two a

example (a : Fin 3 → ℝ) : LipschitzWith 1 (distanceCoordinates ∞ a) := by
  simpa using lipschitzWith_distanceCoordinates ∞ a

example : distanceCoordinates 1 (fun _ : Fin 1 => (3 : ℝ)) 1 0 = 2 := by
  norm_num [Real.dist_eq]

example : Module.finrank ℝ ℝ ≤ 1 := by
  apply LipschitzOnWith.finrank_le_of_image_contains_ball
    (s := ball (0 : ℝ) 1) (f := id) (K := 1) (show LipschitzWith 1 (id : ℝ → ℝ) from LipschitzWith.of_dist_le_mul (fun x y => by simp)).lipschitzOnWith
    (y := 0) (r := 1) (by norm_num) (by simp)
  simpa using (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ

example : Fintype.card (Fin 1) ≤ 1 := by
  let a : Fin 1 → ℝ := fun _ => 0
  let y : PiLp 1 (fun _ : Fin 1 => ℝ) := WithLp.toLp 1 (fun _ => 2)
  have hball : ball y (1 / 2) ⊆ distanceCoordinates 1 a '' Ioo (1 : ℝ) 3 := by
    intro w hw
    have hd : dist (w 0) (2 : ℝ) < 1 / 2 :=
      (PiLp.dist_apply_le w y 0).trans_lt hw
    rw [Real.dist_eq, abs_lt] at hd
    have hw1 : 1 < w 0 := by linarith [hd.1]
    have hw3 : w 0 < 3 := by linarith [hd.2]
    refine ⟨w 0, ⟨hw1, hw3⟩, ?_⟩
    apply WithLp.ofLp_injective 1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change dist (w 0) 0 = w 0
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  apply card_le_of_distanceCoordinates_image_contains_ball 1 a (by norm_num) hball
  simpa using (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ

#print axioms Metric.distanceCoordinates
#print axioms Metric.distanceCoordinates_apply
#print axioms Metric.lipschitzWith_distanceCoordinates
#print axioms Metric.lipschitzWith_distanceCoordinates_one
#print axioms Metric.lipschitzWith_distanceCoordinates_two
#print axioms LipschitzOnWith.finrank_le_dimH_of_image_has_interior
#print axioms LipschitzOnWith.finrank_le_of_image_contains_ball
#print axioms Metric.card_le_dimH_of_distanceCoordinates_image_has_interior
#print axioms Metric.card_le_of_distanceCoordinates_image_contains_ball
```
