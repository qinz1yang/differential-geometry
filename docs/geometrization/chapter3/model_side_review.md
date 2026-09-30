# Compiled self-review: model sides and infinite cradle limit

Nineteen public theorems, one definition and two private identities add 25
owned declarations. The 156-module gate passes for 868 owned declarations,
with only propext, Classical.choice and Quot.sound in their transitive closures.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable at this pin, so declaration kinds were inspected manually.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier
warning is outside these closures. The static audit passes; no migrated
full-root, PDF or Overleaf build is claimed.

The compiled driver checks zero arms, zero and straight angles, both inverse
relations including a zero opposite side, nondegenerate negative-curvature
and collinear Euclidean extension, oscillating arms with angles approaching
pi without individual arm limits, and a concrete infinite recurrence with
all premises supplied. The final consumer explicitly assumes nonincrease
of actual model sides; geometric construction and propagation remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.ModelSideExtension
import DifferentialGeometry.Geometry.Comparison.CradleSideLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Set Filter Topology Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

example : modelSideNegCurvature 2 0 3 (Real.pi / 7) = 3 :=
  modelSideNegCurvature_zero_left (by norm_num) (by norm_num)

example : modelSideNegCurvature 0 2 3 0 = 1 := by
  rw [modelSideNegCurvature_zero_angle (by norm_num)]
  norm_num

example : modelSideNegCurvature 2 2 3 Real.pi = 5 := by
  rw [modelSideNegCurvature_pi (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : modelSideNegCurvature 2 2 2 (comparisonAngleNegCurvature 2 2 2 0) = 0 := by
  apply modelSideNegCurvature_comparisonAngle <;> norm_num

example : comparisonAngleNegCurvature 2 2 3
    (modelSideNegCurvature 2 2 3 (Real.pi / 3)) = Real.pi / 3 := by
  apply comparisonAngleNegCurvature_modelSide <;> try norm_num
  constructor <;> linarith [Real.pi_pos]

example : modelSideNegCurvature 2 2 3 (comparisonAngleNegCurvature 2 2 1 2) =
    modelSideNegCurvature 2 2 2 (Real.pi - comparisonAngleNegCurvature 2 2 1 2) := by
  have h := modelSideNegCurvature_extension_identity (κ := 2) (a := 2) (b := 3) (h := 1) (c := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : modelSideNegCurvature 0 2 3 (comparisonAngleNegCurvature 0 2 1 1) =
    modelSideNegCurvature 0 1 2 (Real.pi - comparisonAngleNegCurvature 0 1 1 2) := by
  have h := modelSideNegCurvature_extension_identity (κ := 0) (a := 2) (b := 3) (h := 1) (c := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

noncomputable def oscillatingSideArm (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 2

private theorem arm_window (n : ℕ) : oscillatingSideArm n ∈ Icc (0 : ℝ) 2 := by
  unfold oscillatingSideArm
  split <;> norm_num

example {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun n : ℕ => oscillatingSideArm n + 1 - modelSideNegCurvature κ
      (oscillatingSideArm n) 1 (Real.pi - Real.pi * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_modelSideNegCurvature_deficit_of_angle_pi (L := 2) hκ
  · apply Eventually.of_forall
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hlo : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hhi : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have hπlo := mul_nonneg Real.pi_pos.le hlo
    have hπhi := mul_le_mul_of_nonneg_left hhi Real.pi_pos.le
    rw [mul_one] at hπhi
    exact ⟨arm_window n, by norm_num, by constructor <;> linarith⟩
  · simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hsmall.const_mul Real.pi)

example {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ _ : ℕ, 14 ≤ modelSideNegCurvature κ 6 8 Real.pi := by
  apply le_modelSideNegCurvature_of_cradle_recurrence
    (a := fun _ => 6) (b := fun _ => 8) (c := fun _ => 8) (α := fun _ => Real.pi)
    (ℓ := 18) (D := 14) hκ (by norm_num)
  · intro n; norm_num
  · intro n; norm_num
  · intro n; norm_num
  · intro n; norm_num
  · intro n; exact ⟨Real.pi_pos.le, le_rfl⟩
  · intro n; exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2
  · intro n m hnm; exact le_rfl
  · intro n; norm_num

#print axioms modelSideNegCurvature_comparisonAngle
#print axioms modelSideNegCurvature_extension_identity
#print axioms modelSideNegCurvature_le_of_adjacent_comparisons
#print axioms le_modelSideNegCurvature_of_cradle_recurrence
```
