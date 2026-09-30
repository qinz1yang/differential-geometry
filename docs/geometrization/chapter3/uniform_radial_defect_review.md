# Compiled self-review: uniform radial defects

Five public theorems pass the scoped compiler and axiom gate. Eta precedes
the metric-space, comparison-domain and point quantifiers. The proof chooses
counterexamples at 1/(n+1), reuses the accepted distance-array subsequence,
passes comparison at positive central sides, and quotients zero-distance
labels by Mathlib SeparationQuotient before applying AC30. All matrix
distances are retained. No source compactness is assumed.

The driver obtains ONE eta for every r in [1,2] and every pair of real
near-radial points satisfying the defects, tests angle continuity at a
straight degenerate triangle, and applies the quotient theorem to identical
points represented by different labels. It compiles with only standard
axiom reports. Source-copy `unusedArguments simpNF synTaut` lints are silent.
`defLemma` is unavailable; declaration kinds were checked manually.
Closures use only propext, Classical.choice and Quot.sound. Earlier math
leaves, including the reused distance-array file, are unchanged. The inherited
AreaUpperBarrier admission warning remains outside the new closures.
This is self-review, not human approval; no full migrated root or PDF build.

```lean
import DifferentialGeometry.Geometry.Comparison.UniformRadialDefect
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

example : ∃ η : ℝ, 0 < η ∧ ∀ r ∈ Icc (1 : ℝ) 2, ∀ u v : ℝ,
    dist 0 u = (1 / 2) * r → r / 2 ≤ dist u r → dist u r ≤ r / 2 + η →
    dist 0 v = (1 / 2) * r → r / 2 ≤ dist v (-r) → dist v (-r) ≤ r / 2 + η →
    (((1 / 2) * 2 / sinh 2) / 2) * dist r (-r) ≤ dist u v := by
  obtain ⟨η, hη, h⟩ := exists_uniform_radial_defect (a := 1) (D := 2)
    (t := 1 / 2) (ε := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨η, hη, ?_⟩
  intro r hr u v hqu huxlo huxhi hqv hvylo hvyhi
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hdist : dist (0 : ℝ) r = r := by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hr0]
  have hdist' : dist (0 : ℝ) (-r) = r := by rw [Real.dist_eq, zero_sub, neg_neg, abs_of_nonneg hr0]
  have hsep : 1 ≤ dist r (-r) := by
    rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (by positivity)]
    linarith [hr.1]
  apply h real_comparison (q := 0) (x := r) (y := -r)
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
  · rwa [hdist]
  · rwa [hdist']
  · exact hsep
  · rwa [hdist]
  · rw [hdist]
    norm_num
    linarith [huxlo]
  · rw [hdist]
    norm_num
    linarith [huxhi]
  · rwa [hdist']
  · rw [hdist']
    norm_num
    linarith [hvylo]
  · rw [hdist']
    norm_num
    linarith [hvyhi]

example (c : ℕ → ℝ) (hc : Filter.Tendsto c Filter.atTop (𝓝 (2 : ℝ))) :
    Filter.Tendsto (fun n => comparisonAngleNegCurvature 1 1 1 (c n)) Filter.atTop (𝓝 Real.pi) := by
  have h := tendsto_comparisonAngleNegCurvature_of_pos (κ := 1) (by norm_num)
    (a := fun _ : ℕ => 1) (b := fun _ : ℕ => 1) tendsto_const_nhds
    tendsto_const_nhds hc (by norm_num) (by norm_num)
  have hπ : comparisonAngleNegCurvature 1 1 1 2 = Real.pi := by
    convert comparisonAngleNegCurvature_add (κ := 1) (a := 1) (b := 1)
      (by norm_num) (by norm_num) (by norm_num) using 1
    norm_num
  rwa [hπ] at h

example : (1 / sinh 2) * dist (2 : ℝ) 2 ≤ dist (1 : ℝ) 1 := by
  let p : Fin 5 → ℝ := ![0, 2, 2, 1, 1]
  have hcomp : ∀ q x y z : Fin 5, 0 < dist (p q) (p x) →
      0 < dist (p q) (p y) → 0 < dist (p q) (p z) →
      comparisonAngleNegCurvature 1 (dist (p q) (p x)) (dist (p q) (p y)) (dist (p x) (p y)) +
        comparisonAngleNegCurvature 1 (dist (p q) (p y)) (dist (p q) (p z)) (dist (p y) (p z)) +
        comparisonAngleNegCurvature 1 (dist (p q) (p z)) (dist (p q) (p x)) (dist (p z) (p x)) ≤ 2 * Real.pi := by
    intro q x y z hx hy hz
    exact real_comparison (p q) (mem_univ _) (p x) (mem_univ _) (p y) (mem_univ _) (p z) (mem_univ _)
      (dist_pos.mp hx).symm (dist_pos.mp hy).symm (dist_pos.mp hz).symm
  have h := radial_lower_of_distance_matrix (fun i j => dist (p i) (p j))
    (fun i => dist_self _) (fun i j => dist_comm _ _) (fun i j k => dist_triangle _ _ _) hcomp
    (q := 0) (x := 1) (y := 2) (u := 3) (v := 4) (D := 2) (t := 1 / 2)
    (by norm_num [p, Real.dist_eq]) (by norm_num [p, Real.dist_eq])
    (by norm_num [p, Real.dist_eq]) (by norm_num [p, Real.dist_eq]) (by norm_num)
    (by norm_num [p, Real.dist_eq]) (by norm_num [p, Real.dist_eq])
    (by norm_num [p, Real.dist_eq]) (by norm_num [p, Real.dist_eq])
  convert h using 1 <;> norm_num [p]

#print axioms exists_uniform_radial_defect
#print axioms exists_uniform_radial_defect_distance_matrix
#print axioms fourPoint_distance_matrix_limit
#print axioms radial_lower_of_distance_matrix

```
