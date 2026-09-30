# Compiled self-review: canonical germs and cradle centers

Fourteen public theorems and one definition add 15 owned declarations.
The 159-module gate passes for 883 owned declarations, with only propext,
Classical.choice and Quot.sound in their transitive closures. Source-copy
unusedArguments, simpNF and synTaut linters are silent; defLemma is unavailable,
and declaration kinds were inspected manually. Earlier mathematical leaves
are unchanged. The inherited AreaUpperBarrier warning remains outside these
closures. Static audit passes; no migrated full-root, PDF or Overleaf build
is claimed.

The compiled driver checks two curves that agree near zero and differ
outside that interval; actual opposite directions with negative-curvature
comparison; and a joint limit for segments of lengths two and three with
only the comparison neighborhood (-1,1). Both full segments leave that
neighborhood. It constructs the actual center x'=2 for endpoints6,8,
old center0 and ell18, and verifies containment of the entire segment[0,8].
The real-line four-point premise is proved directly in the driver.
These examples exercise nonempty geometric data, rather than assumed output
witnesses. The geometric iteration and final globalization remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.CanonicalLocalAngle
import DifferentialGeometry.Topology.MetricSpace.CradleStep
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


private theorem positive_radial {R : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    dist (0 : ℝ) s = s := by
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs.1]

private theorem negative_radial {R : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    dist (0 : ℝ) (-s) = s := by
  rw [Real.dist_eq, sub_neg_eq_add, zero_add, abs_of_pos hs.1]

private theorem opposite_distance {R S : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) S) : dist s (-t) = s + t := by
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_pos (add_pos hs.1 ht.1)]

example : germComparisonAngle 2 (id : ℝ → ℝ)
    (fun t => if t ≤ 1 then t else -t) = 0 := by
  calc
    _ = germComparisonAngle 2 (id : ℝ → ℝ) id :=
      germComparisonAngle_congr_on (r := 1) (s := 1) (by norm_num) (by norm_num)
        (fun _ _ => rfl) (fun t ht => by simp [ht.2])
    _ = 0 := germComparisonAngle_self (R := 1) (by norm_num) (by norm_num)
      (fun s _ t _ => Real.dist_eq s t)

example : germComparisonAngle 2 (id : ℝ → ℝ) (fun t => -t) = Real.pi :=
  germComparisonAngle_opposite (R := 2) (S := 3) (by norm_num) (by norm_num)
    (by norm_num) opposite_distance

example : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature 2 z.1 z.2
    (dist z.1 (-z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (germComparisonAngle 2 (id : ℝ → ℝ) (fun t => -t))) := by
  have hcomp : fourPointComparison 2 (Ioo (-1 : ℝ) 1) := by
    intro x hx a ha b hb c hc hax hbx hcx
    exact real_comparison (by norm_num) x (mem_univ _) a (mem_univ _)
      b (mem_univ _) c (mem_univ _) hax hbx hcx
  have h := tendsto_germComparisonAngle_of_local_fourPointComparison
    (R := 2) (S := 3) (p := (0 : ℝ)) (γ := id) (β := fun t : ℝ => -t) (by norm_num) (by norm_num) (by norm_num)
    isOpen_Ioo hcomp (by norm_num) positive_radial negative_radial
    (fun s _ t _ => Real.dist_eq s t)
    (fun s _ t _ => by rw [dist_neg_neg]; exact Real.dist_eq s t)
  simpa only [id_eq] using h

example : ∃ x' ∈ Icc (0 : ℝ) 8, x' = 2 ∧ x' ∈ ball 6 18 ∩ ball 8 18 := by
  obtain ⟨x', ⟨t, rfl⟩, hx, hv, hlo, hhi, hlt, hs₁, hs₂, hsum, hmem⟩ :=
    Metric.exists_cradle_step_on_segment (x := (0 : ℝ)) (u := 6) (v := 8)
      (ℓ := 18) (by norm_num) (by norm_num [Real.dist_eq])
      (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
      (fun t => (t : ℝ)) isometry_subtype_coe rfl (by norm_num [Real.dist_eq])
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) 8 := by simpa [Real.dist_eq] using t.property
  refine ⟨t, ht, ?_, hmem⟩
  norm_num [Real.dist_eq, abs_of_nonneg ht.1] at hx
  exact hx

example : (Icc (0 : ℝ) 8) ⊆ ball 8 18 ∩ ball 6 18 := by
  have h := Metric.range_segment_subset_endpoint_balls
    (x := (0 : ℝ)) (u := 8) (v := 6) (ℓ := 18) (by norm_num [Real.dist_eq])
    (fun t => (t : ℝ)) isometry_subtype_coe rfl (by norm_num [Real.dist_eq])
  intro t ht
  apply h
  exact ⟨⟨t, by simpa [Real.dist_eq] using ht⟩, rfl⟩

#print axioms germComparisonAngle_congr_on
#print axioms tendsto_germComparisonAngle_of_local_fourPointComparison
#print axioms germComparisonAngle_adjacent_sum_le_pi_of_local_fourPointComparison
#print axioms Metric.exists_cradle_step_on_segment
#print axioms Metric.range_segment_subset_endpoint_balls
```
