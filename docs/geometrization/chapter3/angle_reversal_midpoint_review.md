# AC24–AC25 compiled self-review

This is assistant self-review, not independent human/agent approval.
Reversal applies AC19 at both actual endpoints, retaining the opposite signs
of the distance differences. The inverse-cosine estimate covers zero and pi;
no derivative of arccos near an endpoint is assumed. Both complement bounds
use four-point comparison on one common domain and nearly opposite anchors
at both endpoints. Noncoincidence follows from the positive distance bounds.

The balanced point lies on the supplied curve. Its two distances are exactly
equal, with strict length excess giving a strict angle lower bound. Neither
an exact midpoint nor a minimizing path is assumed. The hyperbolic model law
includes a degenerate triangle, so an exact midpoint remains admissible.
The positive excess constant and all normalization/scale bounds are proved.
The metric construction allows coincident endpoints; the multiplicative
consumer excludes them explicitly. The scalar angle bound does not require
tau<=1; that condition remains in the geometric production of nu>0.

All five new leaves and source-copy unusedArguments, simpNF and synTaut
linters compile silently. defLemma is absent in this pin; declaration kinds
were inspected manually. The 90-module gate passes (2878 jobs, 654 owned
constants), checking the private theorem and every transitive axiom. Only
propext, Classical.choice and Quot.sound occur in new closures. The inherited
AreaUpperBarrier admission warning is outside those closures. Earlier leaves
are unchanged, and no migrated full-root build is claimed.

The static blueprint audit passes unchanged (BLUEPRINT_STATIC_OK); frozen207
is preserved. The examples below check the inverse-cosine boundary pair
0/pi, actual real-line reversal and complement bounds, the full AC25
construction from proved short-curve inputs, and a constant curve with
coincident endpoints. The review driver compiles without warnings.

```lean
import DifferentialGeometry.Geometry.Comparison.AngleReversal
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal
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

private theorem real_anchor_bounds (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) (c : ℝ)
    (hc : c ∈ ({2, -2} : Set ℝ)) : dist z c ∈ Icc (1 : ℝ) 3 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0)]
    constructor <;> linarith [hz.1, hz.2]
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
    constructor <;> linarith [hz.1, hz.2]

private theorem real_packet : PairedComparisonPacket (1 / 200) (Ioo (-1 : ℝ) 1)
    (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (-2 : ℝ)) := by
  constructor
  · intro z hz i
    have heq : dist (2 : ℝ) (-2) = dist z 2 + dist z (-2) := by
      rw [Real.dist_eq (2 : ℝ) (-2), Real.dist_eq z 2, Real.dist_eq z (-2),
        abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0),
        abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
      norm_num
      ring
    rw [heq, comparisonAngleNegCurvature_add (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz 2 (by simp)).1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz (-2) (by simp)).1)]
    linarith
  · intro z hz i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

example : |(0 : ℝ) - Real.pi| ≤ Real.pi * sqrt 1 := by
  apply abs_sub_le_pi_mul_sqrt_of_abs_cos_sub_le
    (by constructor <;> linarith [Real.pi_pos])
    (by constructor <;> linarith [Real.pi_pos])
  norm_num

example :
    |comparisonAngleNegCurvature 1 (dist (1/4 : ℝ) 2) (dist (1/4 : ℝ) 0) (dist (2 : ℝ) 0) +
      comparisonAngleNegCurvature 1 (dist (0 : ℝ) 2) (dist (0 : ℝ) (1/4)) (dist (2 : ℝ) (1/4)) - Real.pi| ≤
      Real.pi * sqrt ((4 * cosh (3 + 1) / sinh 1) * dist (0 : ℝ) (1/4)) := by
  apply abs_comparisonAngleNegCurvature_sum_sub_pi_le
  all_goals norm_num [Real.dist_eq]

example :
    let ω := Real.pi * sqrt ((4 * cosh (3 + 1) / sinh 1) * dist (0 : ℝ) (1/4))
    Real.pi - (1/100) - 2 * ω ≤
      comparisonAngleNegCurvature 1 (dist (1/4 : ℝ) 2) (dist (1/4 : ℝ) 0) (dist (2 : ℝ) 0) +
      comparisonAngleNegCurvature 1 (dist (1/4 : ℝ) (-2)) (dist (1/4 : ℝ) 0) (dist (-2 : ℝ) 0) ∧
      comparisonAngleNegCurvature 1 (dist (1/4 : ℝ) 2) (dist (1/4 : ℝ) 0) (dist (2 : ℝ) 0) +
      comparisonAngleNegCurvature 1 (dist (1/4 : ℝ) (-2)) (dist (1/4 : ℝ) 0) (dist (-2 : ℝ) 0) ≤ Real.pi + 1/100 := by
  have hp := real_packet.weaken (show (1/200 : ℝ) ≤ 1/100 by norm_num)
  apply comparisonAngleNegCurvature_complement_bounds real_comparison
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (by norm_num)
  all_goals first | exact hp.opposite _ (by norm_num) 0 | norm_num [Real.dist_eq]

example : ∃ z : ℝ, dist (0 : ℝ) z = dist (1 : ℝ) z ∧
    Real.pi - 1/100 < comparisonAngleNegCurvature 1 (dist z 0) (dist z 1) (dist (0 : ℝ) 1) := by
  obtain ⟨_, z, heq, _, _, _, hang⟩ := exists_balanced_midpoint_with_comparison_angle
    real_short_curves (0 : ℝ) 1 (τ := 1/100) (by norm_num [Real.dist_eq])
      (by norm_num [Real.dist_eq]) (by norm_num) (by norm_num)
  exact ⟨z, heq, hang⟩

example : ∃ _t : unitInterval, dist (0 : ℝ) 0 = dist (0 : ℝ) 0 ∧
    dist (0 : ℝ) 0 / 2 ≤ dist (0 : ℝ) 0 ∧ dist (0 : ℝ) 0 < (dist (0 : ℝ) 0 + 1) / 2 := by
  exact exists_balanced_midpoint_of_curve (by norm_num : (0 : ℝ) < 1)
    (fun _ => (0 : ℝ)) continuous_const rfl rfl (by
      rw [eVariationOn.constant_on (by simp)]
      simp)

#print axioms abs_comparisonAngleNegCurvature_sum_sub_pi_le
#print axioms comparisonAngleNegCurvature_complement_bounds
#print axioms exists_balanced_midpoint_with_comparison_angle
#print axioms Real.sq_sub_le_pi_sq_mul_abs_cos_sub
```
