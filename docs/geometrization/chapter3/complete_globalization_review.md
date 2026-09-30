# Compiled self-review: complete geodesic globalization

Seven public theorems and one generated declaration add eight owned declarations.
The 181-module gate passes for 976 owned declarations, with only propext,
Classical.choice and Quot.sound in every new transitive axiom closure.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable and declaration kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no full migrated root,
PDF or Overleaf build is claimed.

The compiled driver supplies actual real-line joins and bounded local
comparison neighborhoods Ioo(z-1,z+1). It applies the new global headlines
to a supplied hinge with arms six and eight, repeated outer points, positive
and zero-arm point-on-side configurations, and independent radial parameters
whose full segments leave those local neighborhoods. The local hypotheses
are instantiated from a direct proof of real-line comparison. The original
review script had an id simplification error; the corrected script below
compiled with exit zero. No headline proof was changed to repair that script.

Statement audit: no global endpoint comparison is assumed. The capped-radius
contradiction uses strict-below witnesses, not supremum attainment. Complete
metric space and actual all-pairs segments are explicit inputs. Three chosen
segments are shared across the four-point angle sum. The point-on-side
consumer includes degenerate cases. This is self-review, not an independent
human or delegated review. ALG05 and intrinsic transfer remain separate.

```lean
import DifferentialGeometry.Geometry.Comparison.CompleteComparisonConsequences
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


private theorem real_segment (x y : ℝ) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → ℝ, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  by_cases hxy : x ≤ y
  · refine ⟨fun t => x + (t : ℝ), ?_, by simp, ?_⟩
    · apply Isometry.of_dist_eq
      intro s t
      change |x + (s : ℝ) - (x + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
      congr 1
      ring
    · change x + dist x y = y
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
  · refine ⟨fun t => x - (t : ℝ), ?_, by simp, ?_⟩
    · apply Isometry.of_dist_eq
      intro s t
      change |x - (s : ℝ) - (x - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
      rw [show x - (s : ℝ) - (x - (t : ℝ)) = -((s : ℝ) - (t : ℝ)) by ring, abs_neg]
    · change x - dist x y = y
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
      ring

private def large_hinge : MinimizingHinge (6 : ℝ) 8 where
  center := 0
  left := fun t => t
  right := fun t => t
  left_isometry := isometry_subtype_coe
  right_isometry := isometry_subtype_coe
  left_zero := rfl
  right_zero := rfl
  left_end := by norm_num [Real.dist_eq]
  right_end := by norm_num [Real.dist_eq]

private theorem real_local {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ z : ℝ, ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  intro z
  refine ⟨Ioo (z - 1) (z + 1), isOpen_Ioo, (real_comparison hκ).mono (subset_univ _), ?_⟩
  constructor <;> linarith

example : dist (6 : ℝ) 8 ≤ large_hinge.modelSide 2 :=
  MinimizingHinge.modelSide_ge_dist_of_complete_local_comparison
    (by norm_num) real_segment (real_local (by norm_num)) large_hinge

example : comparisonAngleNegCurvature 2 6 8 2 ≤ large_hinge.germAngle 2 := by
  have h := large_hinge.comparisonAngle_le_of_complete_local_comparison
    (κ := 2) (by norm_num) real_segment (real_local (by norm_num))
    (by norm_num [large_hinge, Real.dist_eq]) (by norm_num [large_hinge, Real.dist_eq])
  norm_num [large_hinge, Real.dist_eq] at h ⊢
  exact h

example {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) :=
  fourPointComparison_of_complete_local_comparison hκ real_segment (real_local hκ)

example : comparisonAngleNegCurvature 2 1 1 0 + comparisonAngleNegCurvature 2 1 2 3 +
    comparisonAngleNegCurvature 2 2 1 3 ≤ 2 * Real.pi := by
  have h := fourPointComparison_of_complete_local_comparison
    (κ := 2) (by norm_num) real_segment (real_local (by norm_num))
    (0 : ℝ) (mem_univ _) 1 (mem_univ _) 1 (mem_univ _) (-2) (mem_univ _)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.dist_eq] at h
  exact h

example : modelSideNegCurvature 2 2 6 (comparisonAngleNegCurvature 2 8 6 2) ≤ 4 := by
  have h := point_on_side_comparison_of_complete_local_comparison
    (κ := 2) (by norm_num) real_segment (real_local (by norm_num))
    (q := (0 : ℝ)) (u := 2) (x := 8) (z := 6) (by norm_num [Real.dist_eq])
  norm_num [Real.dist_eq] at h
  exact h

example : modelSideNegCurvature 2 0 6 (comparisonAngleNegCurvature 2 8 6 2) ≤ 6 := by
  have h := point_on_side_comparison_of_complete_local_comparison
    (κ := 2) (by norm_num) real_segment (real_local (by norm_num))
    (q := (0 : ℝ)) (u := 0) (x := 8) (z := 6) (by norm_num [Real.dist_eq])
  norm_num [Real.dist_eq] at h
  exact h

example : modelSideNegCurvature 2 2 0 (comparisonAngleNegCurvature 2 8 0 8) ≤ 2 := by
  have h := point_on_side_comparison_of_complete_local_comparison
    (κ := 2) (by norm_num) real_segment (real_local (by norm_num))
    (q := (0 : ℝ)) (u := 2) (x := 8) (z := 0) (by norm_num [Real.dist_eq])
  norm_num [Real.dist_eq] at h
  exact h

example : DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn 2 3
    (fun s t : ℝ => comparisonAngleNegCurvature 2 s t (dist s (-t))) := by
  have h := independent_radial_monotonicity_of_complete_local_comparison
    (κ := 2) (R := 2) (S := 3) (p := (0 : ℝ)) (γ := id) (β := fun t : ℝ => -t)
    (by norm_num) real_segment (real_local (by norm_num))
    (fun s hs => by simp only [id_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs.1])
    (fun t ht => by rw [Real.dist_eq, sub_neg_eq_add, zero_add, abs_of_pos ht.1])
    (fun s _ t _ => Real.dist_eq s t)
    (fun s _ t _ => by rw [dist_neg_neg]; exact Real.dist_eq s t)
  simpa only [id_eq] using h

#print axioms MinimizingHinge.modelSide_ge_dist_of_complete_local_comparison
#print axioms endpointHingeComparison_of_complete_local_comparison
#print axioms fourPointComparison_of_complete_local_comparison
#print axioms point_on_side_comparison_of_complete_local_comparison
#print axioms independent_radial_monotonicity_of_complete_local_comparison
```
