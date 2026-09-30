# Compiled self-review: quantitative cradle recurrence

Five public theorems, one private arithmetic theorem and generated declarations
add nine owned declarations. The 152-module/843-owned-declaration gate passes;
transitive closures use only propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent.
defLemma is unavailable; declaration kinds were inspected manually.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier
warning remains outside these closures. Static audit passes; no full migrated
root, PDF or Overleaf build is claimed.

The compiled review exercises actual oscillating arms (alternating one and
two), with a nonzero vanishing deficit 1/(n+1). It supplies no individual
arm-limit hypothesis. It also supplies concrete exact cradle recurrences
ell=18, a=6, b=8, c=8 for curvature zero and curvature minus two, checking
nonempty admissible data and the degenerate straight-triangle case.
The recurrence theorem derives sorted late arm bounds and deficit convergence
before applying uniform positive-window continuity. The threshold is selected
before side data, with curvature fixed. The conclusion is actual Tendsto,
not an extracted-subsequence result. The scalar recurrence hypotheses are
explicit: geometric step construction and germ-angle propagation remain
separate work. This is self-review, not human approval or a complete cradle
or globalization theorem.

```lean
import DifferentialGeometry.Geometry.Comparison.CradleSequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Set Filter Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def oscillatingArm (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 2

private theorem oscillating_arm_window (n : ℕ) : oscillatingArm n ∈ Icc (1 : ℝ) 2 := by
  unfold oscillatingArm
  split <;> norm_num

example {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun n : ℕ => comparisonAngleNegCurvature κ (oscillatingArm n) 1
      (oscillatingArm n + 1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 Real.pi) := by
  apply tendsto_comparisonAngleNegCurvature_pi_of_deficit hκ (by norm_num : (0 : ℝ) < 1)
    (Lmax := 2)
  · apply Eventually.of_forall
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hd : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hden).mpr (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    refine ⟨oscillating_arm_window n, by norm_num, ?_, ?_⟩
    · linarith [(oscillating_arm_window n).1]
    · have := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hden.le
      linarith
  · have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert hlim using 1
    funext n
    ring

example : Tendsto (fun _ : ℕ => comparisonAngleNegCurvature 2 6 2 8) atTop (𝓝 Real.pi) := by
  have h := tendsto_comparisonAngleNegCurvature_pi_of_cradle_recurrence
    (κ := 2) (ℓ := 18) (a := fun _ => 6) (b := fun _ => 8) (c := fun _ => 8)
    (by norm_num) (by norm_num) (by intro n; norm_num) (by intro n; norm_num)
    (by intro n; norm_num) (by intro n; norm_num)
  norm_num at h ⊢
  exact h

example : Tendsto (fun _ : ℕ => comparisonAngleNegCurvature 0 6 2 8) atTop (𝓝 Real.pi) := by
  have h := tendsto_comparisonAngleNegCurvature_pi_of_cradle_recurrence
    (κ := 0) (ℓ := 18) (a := fun _ => 6) (b := fun _ => 8) (c := fun _ => 8)
    (by norm_num) (by norm_num) (by intro n; norm_num) (by intro n; norm_num)
    (by intro n; norm_num) (by intro n; norm_num)
  norm_num at h ⊢
  exact h

#print axioms comparisonAngleNegCurvature_uniform_stability_on_side_window
#print axioms cradle_recurrence_deficit_and_arms
#print axioms tendsto_comparisonAngleNegCurvature_pi_of_cradle_recurrence

```
