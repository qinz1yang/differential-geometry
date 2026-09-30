# Compiled self-review: exact finite radial comparison

Eight public theorems, five private proof helpers and generated declarations
pass the compiler/axiom gate. All closures contain only propext,
Classical.choice and Quot.sound. New source-copy `unusedArguments simpNF
synTaut` lints pass silently. `defLemma` is absent in this pin; declaration
kinds were checked manually. Earlier mathematical leaves are unchanged.
The scoped build replays the inherited AreaUpperBarrier admission warning,
outside these new closures; no full migrated root build was run.

The review applies AC30 to opposite real rays using comparison restricted
to precisely the five-point set, tests coincident outer/radial points, tests
the side inequality with z=u, and applies the pure model result with one
zero radial side for every t in [0,1], including both endpoints. The final
metric theorem does not assume curves, geodesics, compactness, completeness
or pairwise distinct labels. It retains the exact project constant.

The model proof uses a direct sinh convexity argument equivalent to the
written arsinh step. It never assumes a model-triangle realization. This
is compiled self-review, not human approval. Full AC31–33 remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.FiniteRadialComparison
import DifferentialGeometry.Geometry.Comparison.RankExclusionChart
import DifferentialGeometry.Geometry.Comparison.PairedPacketDimension
import DifferentialGeometry.Geometry.Comparison.PairedRankIncrease
import DifferentialGeometry.Geometry.Comparison.AngleReversal
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature 1 (dist x a) (dist x b) (dist a b) = 0 := by
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
  exact comparisonAngleNegCurvature_abs_sub (by norm_num) (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison : fourPointComparison 1 (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc 1 (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 1 (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 1 (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith

example : (1 / sinh 2) * 4 ≤ (2 : ℝ) := by
  have h := dist_radial_points_lower_of_fourPointComparison
    (real_comparison.mono (subset_univ ({0, 2, -2, 1, -1} : Set ℝ)))
    (q := 0) (x := 2) (y := -2) (u := 1) (v := -1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (D := 2) (t := 1 / 2) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq]) (by norm_num)
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
  simpa only [Real.dist_eq, sub_neg_eq_add] using (by norm_num [Real.dist_eq] at h ⊢; exact h)

example : (1 / sinh 2) * dist (2 : ℝ) 2 ≤ dist (1 : ℝ) 1 := by
  have h := dist_radial_points_lower_of_fourPointComparison real_comparison
    (q := 0) (x := 2) (y := 2) (u := 1) (v := 1)
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
    (D := 2) (t := 1 / 2) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq]) (by norm_num)
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
  convert h using 1
  norm_num

example : sinh (dist (1 : ℝ) 2) * cosh (dist (0 : ℝ) 1) +
    sinh (dist (0 : ℝ) 1) * cosh (dist (2 : ℝ) 1) ≤
    sinh (dist (0 : ℝ) 2) * cosh (dist (1 : ℝ) 1) :=
  hyperbolic_side_comparison_of_fourPointComparison real_comparison
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])

example {t : ℝ} (ht : t ∈ Icc 0 1) : t / sinh 1 ≤ t := by
  have h := radial_side_lower_of_cosine_laws (r := 1) (s := 0) (c := 1) (d := t)
    (D := 1) (t := t) (C := 1) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) ht.1 (by norm_num) ht le_rfl (by simp) (by simp)
  simpa only [mul_one] using h

#print axioms dist_radial_points_lower_of_fourPointComparison
#print axioms comparisonAngleNegCurvature_one_le_of_shortening_left
#print axioms radial_side_lower_of_cosine_laws
#print axioms convexOn_sinh_nonneg

```
