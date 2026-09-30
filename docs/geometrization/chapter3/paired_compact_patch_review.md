# Compiled self-review: compact inner chart patch

Three public theorems and their generated declarations pass the scoped
compiler/axiom gate. The proof uses completeness only of the actual inner
closed ball and properness only of the chart target. Positive radius and
containment in the requested open set are explicit in the geometric output.
No compactness of the source or minimizing-geodesic hypothesis is assumed.

The compiled driver applies the geometric theorem to every real interval
(-s,s), s>0, with a compact positive ambient closed ball as output. Separate
generic consumers cover a negative inner radius (empty ball) and zero inner
radius (singleton). The source-copy `unusedArguments simpNF synTaut` suite
passes silently. `defLemma` is unavailable in this pin; declaration kinds
were manually checked. New closures use only propext, Classical.choice and
Quot.sound; the inherited AreaUpperBarrier warning remains outside them.
Earlier mathematical leaves are unchanged. This is self-review, not human
approval, and no full migrated root or PDF build is claimed.

```lean
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

example {s : ℝ} (hs : 0 < s) : ∃ q ∈ Ioo (-s) s, ∃ r : ℝ,
    0 < r ∧ closedBall q r ⊆ Ioo (-s) s ∧ IsCompact (closedBall q r) :=
  exists_compact_closedBall_in_open_set real_short_curves real_comparison
    (subset_univ _) isOpen_Ioo ⟨0, by constructor <;> linarith⟩
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) le_rfl (by rw [Nat.cast_one, Real.dimH_univ])

example : IsCompact (closedBall (0 : ℝ) (-1)) := by
  apply isCompact_closedBall_of_chart (r := 1) (by norm_num) isClosed_closedBall.isComplete
    (f := fun x => (x : ℝ)) (ε := 1) (C := 1) (by norm_num)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, le_refl]
  · intro x y
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, le_refl]

example : IsCompact (closedBall (0 : ℝ) 0) := by
  apply isCompact_closedBall_of_chart (r := 1) (by norm_num) isClosed_closedBall.isComplete
    (f := fun x => (x : ℝ)) (ε := 1) (C := 1) (by norm_num)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, le_refl]
  · intro x y
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, le_refl]

#print axioms exists_compact_closedBall_in_open_set
#print axioms isCompact_closedBall_of_chart
#print axioms isCompact_of_bounded_bilipschitz_image

```
