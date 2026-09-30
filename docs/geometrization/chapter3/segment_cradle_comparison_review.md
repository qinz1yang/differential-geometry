# Compiled self-review: segment germs and cradle comparison

Ten public theorems add ten owned declarations. The 162-module gate passes
for 893 owned declarations with only propext, Classical.choice and Quot.sound
in the transitive closures. Source-copy unusedArguments, simpNF and synTaut
linters are silent; defLemma is unavailable, and declaration kinds were
inspected manually. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes;
no migrated full-root, PDF or Overleaf build is claimed.

The compiled driver checks the opposite endpoints of the actual segment
[0,8] centered at2, the adjacent sum for a length4 third arm with only local
comparison on(1,3), the between-point stop and a zero-arm stop, and actual
model-side nonincrease for old arms6,8, new arms4,6 and h=2. The two short
comparison premises in this instance are proved from actual model-angle
and germ-distance formulas. Real-line four-point comparison is proved in
the driver. The full all-small-hinges producer and iteration remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.CradleComparison
import Mathlib.Tactic

open Set Filter Topology Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


example : dist (IccExtend (by norm_num : (0 : ℝ) ≤ 8)
    (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 + 6))
    (IccExtend (by norm_num : (0 : ℝ) ≤ 8) (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 - 2)) = 8 := by
  have h := (isometry_subtype_coe : Isometry (fun t : Icc (0 : ℝ) 8 => (t : ℝ))).IccExtend_opposite_dist
    (h := 2) (s := 6) (t := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢

example : germComparisonAngle 2 (fun t : ℝ => 2 + t)
      (fun t => IccExtend (by norm_num : (0 : ℝ) ≤ 8)
        (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 - t)) +
    germComparisonAngle 2 (fun t : ℝ => 2 + t)
      (fun t => IccExtend (by norm_num : (0 : ℝ) ≤ 8)
        (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 + t)) ≤ Real.pi := by
  have hcomp : fourPointComparison 2 (Ioo (1 : ℝ) 3) :=
    (real_comparison (by norm_num)).mono (subset_univ _)
  apply germComparisonAngle_IccExtend_adjacent_sum_le_pi (S := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    isometry_subtype_coe isOpen_Ioo hcomp (by norm_num)
  · intro s hs
    change dist (2 : ℝ) (2 + s) = s
    rw [Real.dist_eq, show (2 : ℝ) - (2 + s) = -s by ring, abs_neg, abs_of_pos hs.1]
  · intro s hs t ht
    rw [Real.dist_eq, show (2 : ℝ) + s - (2 + t) = s - t by ring]

example : (2 : ℝ) ≤ modelSideNegCurvature 2 (dist (0 : ℝ) 6) (dist (0 : ℝ) 8) 0 := by
  have h := dist_le_modelSideNegCurvature_of_between (κ := 2) (θ := 0)
    (x := (0 : ℝ)) (u := 6) (v := 8) (by norm_num)
    ⟨le_rfl, Real.pi_pos.le⟩ (by norm_num [Real.dist_eq])
  simpa only [Real.dist_eq, show |(6 : ℝ) - 8| = 2 by norm_num] using h

example : (8 : ℝ) ≤ modelSideNegCurvature 2 (dist (0 : ℝ) 0) (dist (0 : ℝ) 8) Real.pi := by
  have h := dist_le_modelSideNegCurvature_of_between (κ := 2) (θ := Real.pi)
    (x := (0 : ℝ)) (u := 0) (v := 8) (by norm_num)
    ⟨Real.pi_pos.le, le_rfl⟩ (by simp)
  simpa [Real.dist_eq] using h

#print axioms Isometry.IccExtend_opposite_dist
#print axioms germComparisonAngle_IccExtend_adjacent_sum_le_pi
#print axioms modelSideNegCurvature_cradle_step_le
#print axioms dist_le_modelSideNegCurvature_of_between
example : modelSideNegCurvature 2 4 6
      (germComparisonAngle 2 (fun t : ℝ => 2 + t)
        (fun t => IccExtend (by norm_num : (0 : ℝ) ≤ 8)
          (fun t : Icc (0 : ℝ) 8 => (t : ℝ)) (2 + t))) ≤
    modelSideNegCurvature 2 6 8
      (germComparisonAngle 2 (id : ℝ → ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 8) (fun t : Icc (0 : ℝ) 8 => (t : ℝ)))) := by
  let σ : Icc (0 : ℝ) 8 → ℝ := fun t => t
  have hcomp : fourPointComparison 2 (Ioo (1 : ℝ) 3) :=
    (real_comparison (by norm_num)).mono (subset_univ _)
  have hfirst : comparisonAngleNegCurvature 2 6 2 4 ≤
      germComparisonAngle 2 (id : ℝ → ℝ) (IccExtend (by norm_num : (0 : ℝ) ≤ 8) σ) := by
    have heq : comparisonAngleNegCurvature 2 6 2 4 = 0 := by
      have h := comparisonAngleNegCurvature_abs_sub
        (κ := 2) (a := 6) (b := 2) (by norm_num) (by norm_num) (by norm_num)
      norm_num at h
      exact h
    rw [heq]
    exact (germComparisonAngle_mem_Icc _ _ _).1
  have hsecond : comparisonAngleNegCurvature 2 4 2 6 ≤
      germComparisonAngle 2 (fun t : ℝ => 2 + t)
        (fun t => IccExtend (by norm_num : (0 : ℝ) ≤ 8) σ (2 - t)) := by
    have hπ : germComparisonAngle 2 (fun t : ℝ => 2 + t)
        (fun t => IccExtend (by norm_num : (0 : ℝ) ≤ 8) σ (2 - t)) = Real.pi := by
      apply germComparisonAngle_opposite (R := 4) (S := 2)
        (by norm_num) (by norm_num) (by norm_num)
      intro s hs t ht
      rw [IccExtend_of_mem _ σ (show (2 : ℝ) - t ∈ Icc 0 8 by constructor <;> linarith [ht.1, ht.2])]
      change dist (2 + s) (2 - t) = s + t
      rw [Real.dist_eq, show (2 : ℝ) + s - (2 - t) = s + t by ring,
        abs_of_pos (add_pos hs.1 ht.1)]
    rw [hπ]
    exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2
  have hrad : ∀ s ∈ Ioc (0 : ℝ) 4, dist (2 : ℝ) (2 + s) = s := by
    intro s hs
    rw [Real.dist_eq, show (2 : ℝ) - (2 + s) = -s by ring, abs_neg, abs_of_pos hs.1]
  have hmin : ∀ s ∈ Ioc (0 : ℝ) 4, ∀ t ∈ Ioc (0 : ℝ) 4,
      dist (2 + s) (2 + t) = |s - t| := by
    intro s hs t ht
    rw [Real.dist_eq, show (2 : ℝ) + s - (2 + t) = s - t by ring]
  have H := modelSideNegCurvature_le_of_segment_germ_comparisons
    (a := 6) (h := 2) (σ := σ) (Ω := Ioo (1 : ℝ) 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    isometry_subtype_coe isOpen_Ioo hcomp (by norm_num [σ])
    hrad hmin (by norm_num) (by norm_num) hfirst hsecond
  norm_num at H
  exact H

```
