# Compiled self-review: cradle iteration and actual interval restrictions

Five public theorems add five owned declarations. The 167-module gate passes
for 903 owned declarations with only propext, Classical.choice and Quot.sound
in the transitive closures. Source-copy unusedArguments, simpNF and synTaut
linters are silent; defLemma is unavailable, and declaration kinds were
inspected manually. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes;
no migrated full-root, PDF or Overleaf build is claimed.

The compiled driver supplies Q=Nat with an actual successor q->q+1, arms6,8,
angle pi, ell18, D14 and c8. Every step recurrence and angle inequality is
proved directly; the step witness does not use the hypothetical failing-side
premise, and no sequence is supplied to the theorem. It also checks forward
and backward interval isometries from[0,8] at2, a zero-length restriction at8,
and canonical-angle compatibility for the nonlinear map t->t^2. The latter
checks that compatibility depends on exact initial agreement rather than an
unstated isometry assumption. Geometric state instantiation remains open.

```lean
import DifferentialGeometry.Topology.MetricSpace.SegmentRestriction
import DifferentialGeometry.Geometry.Comparison.SegmentRestrictionAngle
import DifferentialGeometry.Geometry.Comparison.CradleIteration
import Mathlib.Tactic

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

example : ∀ _q : ℕ, (14 : ℝ) ≤ modelSideNegCurvature 2 6 8 Real.pi := by
  apply le_modelSideNegCurvature_of_cradle_steps (Q := ℕ) (ℓ := 18)
    (by norm_num) (by norm_num) (fun _ => 6) (fun _ => 8) (fun _ => Real.pi)
  · intro q hbad
    norm_num
  · intro q
    exact ⟨Real.pi_pos.le, le_rfl⟩
  · intro q
    norm_num
  · intro q hbad
    refine ⟨q + 1, 8, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, ?_⟩
    exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2

example : Isometry (fun s : Icc (0 : ℝ) (8 - 2) =>
    IccExtend (by norm_num : (0 : ℝ) ≤ 8) (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 + s)) :=
  (isometry_subtype_coe : Isometry (fun t : Icc (0 : ℝ) 8 => (t : ℝ))).IccExtend_forward_isometry
    (by norm_num : (2 : ℝ) ∈ Icc (0 : ℝ) 8)

example : Isometry (fun s : Icc (0 : ℝ) (2 - 0) =>
    IccExtend (by norm_num : (0 : ℝ) ≤ 8) (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 - s)) :=
  (isometry_subtype_coe : Isometry (fun t : Icc (0 : ℝ) 8 => (t : ℝ))).IccExtend_backward_isometry
    (by norm_num : (2 : ℝ) ∈ Icc (0 : ℝ) 8)

example : Isometry (fun s : Icc (0 : ℝ) (8 - 8) =>
    IccExtend (by norm_num : (0 : ℝ) ≤ 8) (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (8 + s)) :=
  (isometry_subtype_coe : Isometry (fun t : Icc (0 : ℝ) 8 => (t : ℝ))).IccExtend_forward_isometry
    (by norm_num : (8 : ℝ) ∈ Icc (0 : ℝ) 8)

example : germComparisonAngle 2 (id : ℝ → ℝ)
    (IccExtend (by norm_num : (0 : ℝ) ≤ 8 - 2)
      (fun s : Icc (0 : ℝ) (8 - 2) => IccExtend (by norm_num : (0 : ℝ) ≤ 8)
        (fun t : Icc (0 : ℝ) 8 => (t : ℝ) ^ 2) (2 + s))) =
    germComparisonAngle 2 (id : ℝ → ℝ) (fun s => IccExtend (by norm_num : (0 : ℝ) ≤ 8)
      (fun t : Icc (0 : ℝ) 8 => (t : ℝ) ^ 2) (2 + s)) :=
  germComparisonAngle_IccExtend_forward (by norm_num : (2 : ℝ) ∈ Icc (0 : ℝ) 8)
    (by norm_num) _ _ _

#print axioms le_modelSideNegCurvature_of_cradle_steps
#print axioms Isometry.IccExtend_forward_isometry
#print axioms germComparisonAngle_IccExtend_forward
```
