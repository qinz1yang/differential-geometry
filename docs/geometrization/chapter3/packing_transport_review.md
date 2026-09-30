# Compiled self-review: finite packing transport

Seven public theorems and one definition pass the scoped compiler/axiom
gate. The source-copy `unusedArguments simpNF synTaut` suite is silent.
`defLemma` is unavailable; declaration kinds were checked manually.
The new closures use only propext, Classical.choice and Quot.sound. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
remains outside the new closures; no full migrated-root or PDF build.

The driver checks packing of the empty set and proves that two real points
at distance EXACTLY one have non-strict packing number two at epsilon=1.
It constructs an actual two-point image of {-2,2} inside B(0,3/2), preserving
cardinality and the exact transported separation. This verifies the
strict/non-strict convention and a nonempty geometric consumer.

The annular map uses actual first-hit points; its lower estimate applies
only to pairs separated by at least the chosen epsilon. No continuity or
uniform lower estimate for closer points is asserted. Taking suprema over
finite sets needs no finite packing-value assumption. This is compiled
self-review, not human approval. AC33 and the later chapter work remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.PackingTransport
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

example (ε : ℝ) : finitePackingNumber ε (∅ : Set ℝ) = 0 := by
  apply le_antisymm _ bot_le
  apply finitePackingNumber_le_iff.mpr
  intro A hA _
  have hAempty : A = ∅ := by
    apply Finset.coe_injective
    simpa only [Finset.coe_empty] using Set.eq_empty_of_subset_empty hA
  subst A
  simp

example : finitePackingNumber 1 ({0, 1} : Set ℝ) = 2 := by
  apply le_antisymm
  · apply finitePackingNumber_le_iff.mpr
    intro A hA _
    have hAsub : A ⊆ ({0, 1} : Finset ℝ) := by
      intro x hx
      simpa only [Finset.mem_insert, Finset.mem_singleton, mem_insert_iff, mem_singleton_iff] using hA hx
    have hcard : A.card ≤ 2 := by simpa using Finset.card_le_card hAsub
    exact_mod_cast hcard
  · have hsep : (({0, 1} : Finset ℝ) : Set ℝ).Pairwise (fun x y => (1 : ℝ) ≤ dist x y) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [Real.dist_eq] at *
    have h := card_le_finitePackingNumber ({0, 1} : Finset ℝ) (S := {0, 1}) (by simp) hsep
    simpa using h

example : ∃ B : Finset ℝ, (B : Set ℝ) ⊆ ball (0 : ℝ) (3 / 2) ∧ B.card = 2 ∧
    (B : Set ℝ).Pairwise (fun x y => (((1 / 2) * 2 / sinh 2) / 2) * 4 ≤ dist x y) := by
  have hrad (x : ℝ) (hx : x ∈ ({-2, 2} : Set ℝ)) : dist (0 : ℝ) x ∈ Icc (2 : ℝ) 2 := by
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [Real.dist_eq]
  have hsep : (({-2, 2} : Finset ℝ) : Set ℝ).Pairwise (fun x y => (4 : ℝ) ≤ dist x y) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [Real.dist_eq] at *
  obtain ⟨B, hB, hcard, hBsep⟩ := exists_radial_finset_image real_short_curves real_comparison
    (q := 0) (mem_univ _) (a := 2) (D := 2) (t := 1 / 2) (ρ := 3 / 2) (ε := 4)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (subset_univ _) (subset_univ _) hrad ({-2, 2} : Finset ℝ) (by simp) hsep
  exact ⟨B, hB, by norm_num at hcard; exact hcard, hBsep⟩

#print axioms exists_radial_map_of_arbitrarily_short_curves
#print axioms exists_radial_finset_image
#print axioms finitePackingNumber_le_radial_ball
#print axioms finitePackingNumber_le_of_finite_images

```
