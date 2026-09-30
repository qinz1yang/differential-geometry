# Compiled self-review: endpoint comparison and actual small hinges

Four public theorems and one definition add five owned declarations. The
164-module gate passes for 898 owned declarations; transitive axiom closures
use only propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. defLemma is unavailable; declaration
kinds were inspected manually. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning is outside these closures. Static
audit passes; no migrated full-root, PDF or Overleaf build is claimed.

The compiled driver proves real-line four-point comparison and the actual
endpoint comparison property for EVERY positive radius. It applies the local
uniform producer to the neighborhood(1,3) of2, retaining the endpoint and
radius quantifiers. Its concrete cradle has original center0, endpoints6,8,
new center2, radius12 and the actual supplied joins[0,6],[0,8],[2,6]. Both
short comparisons are produced from endpoint comparison; neither is assumed
as an extra premise. The new center uses only local comparison on(1,3), and
the full joins leave that neighborhood. The geometric iteration remains open.

```lean
import DifferentialGeometry.Geometry.Comparison.CradleSmallHinges
import Mathlib.Tactic

open Set Metric Filter Topology
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


private theorem real_endpoint_comparison {κ : ℝ} (hκ : 0 ≤ κ) (p r : ℝ) :
    endpointHingeComparison κ p r := by
  intro x R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  rw [germComparisonAngle_eq_limitingComparisonAngle hκ hR hS (real_comparison hκ)
    (mem_univ x) hγrad hβrad hγmin hβmin (fun _ _ => mem_univ _) (fun _ _ => mem_univ _), ← hend]
  exact comparisonAngleNegCurvature_le_limitingComparisonAngle γ β ⟨hR, le_rfl⟩ ⟨hS, le_rfl⟩

example : ∃ a : ℝ, 0 < a ∧ ∀ q ∈ ball (2 : ℝ) a, endpointHingeComparison 2 q a := by
  have hcomp : fourPointComparison 2 (Ioo (1 : ℝ) 3) :=
    (real_comparison (by norm_num)).mono (subset_univ _)
  exact exists_uniform_endpointHingeComparison (by norm_num) isOpen_Ioo hcomp (by norm_num)

example : modelSideNegCurvature 2 4 6
      (germComparisonAngle 2 (IccExtend (dist_nonneg : (0 : ℝ) ≤ dist (2 : ℝ) 6)
        (fun t : Icc (0 : ℝ) (dist (2 : ℝ) 6) => 2 + (t : ℝ)))
        (fun t => IccExtend (dist_nonneg : (0 : ℝ) ≤ dist (0 : ℝ) 8)
          (fun t : Icc (0 : ℝ) (dist (0 : ℝ) 8) => (t : ℝ)) (2 + t))) ≤
    modelSideNegCurvature 2 6 8
      (germComparisonAngle 2 (IccExtend dist_nonneg
        (fun t : Icc (0 : ℝ) (dist (0 : ℝ) 6) => (t : ℝ)))
        (IccExtend dist_nonneg (fun t : Icc (0 : ℝ) (dist (0 : ℝ) 8) => (t : ℝ)))) := by
  have hcomp : fourPointComparison 2 (Ioo (1 : ℝ) 3) :=
    (real_comparison (by norm_num)).mono (subset_univ _)
  have hτ : Isometry (fun t : Icc (0 : ℝ) (dist (2 : ℝ) 6) => 2 + (t : ℝ)) := by
    apply Isometry.of_dist_eq
    intro s t
    change |(2 + (s : ℝ)) - (2 + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
    congr 1
    ring
  have H := endpointHingeComparison.cradle_modelSide_le
    (κ := 2) (r := 12) (h := 2) (x := (0 : ℝ)) (u := 6) (v := 8)
    (by norm_num) (real_endpoint_comparison (by norm_num) 6 12)
    (by norm_num [Real.dist_eq]) (by norm_num) (by norm_num [Real.dist_eq])
    (fun t : Icc (0 : ℝ) (dist (0 : ℝ) 6) => (t : ℝ))
    isometry_subtype_coe rfl (by norm_num [Real.dist_eq])
    (fun t : Icc (0 : ℝ) (dist (0 : ℝ) 8) => (t : ℝ))
    isometry_subtype_coe rfl (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (fun t : Icc (0 : ℝ) (dist (2 : ℝ) 6) => 2 + (t : ℝ)) hτ
    (by norm_num) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    isOpen_Ioo hcomp (by norm_num)
  norm_num [Real.dist_eq] at H ⊢
  exact H

#print axioms exists_uniform_endpointHingeComparison
#print axioms endpointHingeComparison.modelSide_ge_dist
#print axioms endpointHingeComparison.cradle_modelSide_le
```
