# Compiled self-review: AC18 and local rough dimension

Nine public theorems and two definitions in four leaves pass the
137-module/797-owned-declaration gate. Source-copy unusedArguments, simpNF
and synTaut linters are silent. defLemma is unavailable; declaration kinds
were inspected manually. The definitions are actual numerical invariants,
not proposition aliases. New closures use only propext, Classical.choice
and Quot.sound. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning remains outside these closures; no migrated-root
or PDF build is claimed. The blueprint static audit passes.

The compiled driver produces a single rough-dimension-controlled ball at
an arbitrary real point, with the same ball for every supercritical
exponent. Empty and singleton rough dimensions are zero. Crucially, the
singleton's critical rough volume at exponent zero is proved to be ONE,
so the definition and proof do not collapse critical behavior into zero.
A concrete nonconstant real interval curve forces dimension at least one
in a positive ball. The final producer allows n=0 and includes the
singleton branch; its positive-rank branch derives 1<=n from actual local
Hausdorff dimension. Positive scales and ENat-to-ENNReal coercion are
explicit throughout. This is self-review, not human approval.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalRoughDimension
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

example (p : ℝ) : ∃ h : ℝ, 0 < h ∧ ball p h ⊆ (univ : Set ℝ) ∧
    ∃ m : ℕ, m ≤ 1 ∧ roughDim (ball p h) ≤ m ∧
      ∀ b : ℝ, (m : ℝ) < b → roughVolume b (ball p h) = 0 := by
  exact exists_local_roughDim_le_of_fourPointComparison real_short_curves
    isOpen_univ real_comparison
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) (by rw [Nat.cast_one, Real.dimH_univ]) (mem_univ p)

example : roughDim (∅ : Set ℝ) = 0 := roughDim_eq_zero_of_subsingleton (by simp)

example (p : ℝ) : roughDim ({p} : Set ℝ) = 0 :=
  roughDim_eq_zero_of_subsingleton (subsingleton_singleton)

example (p : ℝ) : roughVolume 0 ({p} : Set ℝ) = 1 := by
  have hp (ε : ℝ) : finitePackingNumber ε ({p} : Set ℝ) = 1 := by
    apply le_antisymm (finitePackingNumber_le_one_of_subsingleton (subsingleton_singleton) ε)
    have h := card_le_finitePackingNumber ({p} : Finset ℝ) (ε := ε) (S := {p})
      (by simp) (by simp)
    simpa using h
  unfold roughVolume
  simpa only [Real.rpow_zero, ENNReal.ofReal_one, hp, ENat.toENNReal_one, one_mul] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1)).limsup_eq

example : 1 ≤ dimH (ball (0 : ℝ) 1) := by
  apply one_le_dimH_ball_of_continuous_curve (by norm_num) (fun t : unitInterval => (t : ℝ))
    continuous_subtype_val rfl
  norm_num

#print axioms roughVolume_eq_zero_of_polynomial_bound
#print axioms roughDim_le_of_polynomial_bound
#print axioms subsingleton_of_dimH_ball_lt_one
#print axioms exists_local_roughDim_le_of_fourPointComparison

```
