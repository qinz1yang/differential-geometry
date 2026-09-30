# Compiled self-review: prescribed-point compactness

Two public theorems in two leaves pass the 130-module/765-owned-declaration
gate. The source-copy unusedArguments, simpNF and synTaut linters are silent.
defLemma is unavailable; declaration kinds were inspected manually. New
closures contain only propext, Classical.choice and Quot.sound. The inherited
AreaUpperBarrier warning remains outside these closures. Earlier mathematical
leaves are unchanged; no full migrated-root or PDF build is claimed.

The compiled driver applies the theorem at every real p, deriving a positive
compact closed-ball neighborhood from actual curves, comparison and dimension.
It also transports the nonempty annulus [2,3] toward a compact unit ball with
t=1/4. The main proof handles p=q separately and otherwise proves positive
inner radial radius before choosing t. Closed-ball completeness is restricted
explicitly from the given buffer; no global completeness is assumed.
This is self-review, not human approval. Intrinsic metric adaptation and
rough-dimension asymptotics remain separate unfinished work.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalCompactness
import DifferentialGeometry.Geometry.Comparison.PairedCompactPatch
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

private theorem real_short_curves (p u : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
      eVariationOn c univ < ENNReal.ofReal (dist p u + η) := by
  have hmid (a b ε : ℝ) (hε : 0 < ε) :
      ∃ z : ℝ, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε := by
    refine ⟨(a + b) / 2, ?_, ?_⟩
    · have heq : a - (a + b) / 2 = (a - b) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div]
      norm_num
      rw [Real.dist_eq a b]
      linarith
    · have heq : b - (a + b) / 2 = (b - a) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div, abs_sub_comm b a]
      norm_num
      rw [Real.dist_eq a b]
      linarith
  obtain ⟨c, hc, hc0, hc1, _, hlen⟩ := exists_curve_eVariationOn_lt_of_approximate_midpoints
    hmid p u hη
  exact ⟨c, hc, hc0, hc1, hlen⟩

example (p : ℝ) : ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ (univ : Set ℝ) ∧
    IsCompact (closedBall p r) := by
  exact exists_compact_closedBall_at_of_fourPointComparison real_short_curves
    isOpen_univ real_comparison
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) le_rfl (by rw [Nat.cast_one, Real.dimH_univ]) (mem_univ p)

example : TotallyBounded (Icc (2 : ℝ) 3) := by
  apply totallyBounded_annulus_of_compact_radial_target real_short_curves real_comparison
    (q := 0) (mem_univ _) (a := 2) (D := 3) (t := 1 / 4) (ρ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (subset_univ _) (subset_univ _)
  · intro x hx
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)] using hx
  · exact isCompact_closedBall 0 1

#print axioms totallyBounded_annulus_of_compact_radial_target
#print axioms exists_compact_closedBall_at_of_fourPointComparison

```
