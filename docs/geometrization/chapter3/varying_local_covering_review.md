# Compiled self-review: varying-curvature local producers

Five public theorems in two leaves add five owned declarations. The219-module
gate checks1125 declarations (3053 jobs), with only propext, Classical.choice
and Quot.sound in transitive closures. Source-copy unusedArguments, simpNF
and synTaut linters are silent; declaration kinds were inspected manually
because defLemma is unavailable. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning is outside these closures. Static
audit passes. No full migrated root, PDF, Overleaf, human or delegated
review is claimed.

The compiled review applies both covering producers to the real line for
EVERY0<=kappa<=1 and every positive epsilon, deriving the literal rank1
ceiling bound and strict internal coverage of the closed unit ball. Thus
both the zero and positive-curvature branches are inhabited consumers,
without supplied charts or compactness. The intrinsic version names the
actual intrinsic metric and its topology. Local compactness of the open
interval(-5,5) is derived from dimension1 and local comparison for every
nonnegative kappa. The ambient and actual-intrinsic comparison producers
are applied at kappa2, explicitly exercising the absence of a kappa<=1
restriction on comparison. All five applications compile with exit zero;
only axiom reports appear in the final driver log.

Statement audit separates the covering restriction0<=kappa<=1 from the
arbitrary nonnegative parameter allowed for local compactness and the
same-parameter inner-ball comparison. Positive rescaling uses sqrt(kappa),
rescaled radius AND mesh, unchanged dimension and completeness, and the
exact numerical ceiling inequality. The zero branch uses the proved
zero-to-one angle inequality. The final net lies in the original closed
R-ball, covers strictly at epsilon, and has the same fixed-n/L_n bound.
The compactness proof uses preserved subtype topology; the final comparison
returns to the original metric and original kappa. There is no global
properness premise, uniform chart-radius premise, unproved curvature
monotonicity, or sharp8R/KL import. Growing-region tails and extraction
remain a separate assembly on one actual limit.

```lean
import DifferentialGeometry.Geometry.Comparison.VaryingCurvatureCovering
import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalCovering
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

open Set Metric Topology
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


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments real_segments

private theorem ambient_local (z : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  refine ⟨Ioo (z - 1) (z + 1), isOpen_Ioo,
    (real_comparison hκ).mono (subset_univ _), ?_⟩
  exact ⟨by linarith, by linarith⟩

private theorem real_dim_ball : dimH (ball (0 : ℝ) (256 * 1)) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using
    (dimH_mono (subset_univ (ball (0 : ℝ) (256 * 1)))).trans_eq Real.dimH_univ

example {κ ε : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ T : Finset ℝ,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sinh 2 / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, ∃ y ∈ T, dist x y < ε := by
  have h := exists_closedBall_net_of_bounded_local_curvature_and_dimH real_curves 0
    hκ hκ1 (by norm_num : (0 : ℝ) < 1) hε (by omega : 1 ≤ (1 : ℕ)) real_dim_ball
    (fun z _ => ambient_local z hκ)
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

example {κ ε : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ T : Finset ℝ,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sinh 2 / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, ∃ y ∈ T, dist x y < ε := by
  have h := exists_closedBall_net_of_bounded_intrinsic_local_curvature_and_dimH real_curves 0
    hκ hκ1 (by norm_num : (0 : ℝ) < 1) hε (by omega : 1 ≤ (1 : ℕ)) real_dim_ball
    (fun z => (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
      (by norm_num : (0 : ℝ) < 256 * 1) z).mpr (ambient_local z hκ))
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

example {κ : ℝ} (hκ : 0 ≤ κ) : LocallyCompactSpace (Ioo (-5 : ℝ) 5) := by
  have hdim : dimH (Ioo (-5 : ℝ) 5) ≤ (1 : ℕ) := by
    simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (Ioo (-5 : ℝ) 5))).trans_eq Real.dimH_univ
  exact locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
    real_curves hκ isOpen_Ioo hdim (fun z _ => ambient_local z hκ)

example : fourPointComparison 2 (ball (0 : ℝ) (2 * 1)) := by
  exact fourPointComparison_two_ball_of_local_comparison_and_dimH real_curves 0
    (by norm_num) (by norm_num) real_dim_ball (fun z _ => ambient_local z (by norm_num))

example : fourPointComparison 2 (ball (0 : ℝ) (2 * 1)) := by
  exact fourPointComparison_two_ball_of_intrinsic_local_comparison_and_dimH real_curves 0
    (by norm_num) (by norm_num) real_dim_ball
    (fun z => (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
      (by norm_num : (0 : ℝ) < 256 * 1) z).mpr (ambient_local z (by norm_num)))

#print axioms exists_closedBall_net_of_bounded_local_curvature_and_dimH
#print axioms exists_closedBall_net_of_bounded_intrinsic_local_curvature_and_dimH
#print axioms locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
#print axioms fourPointComparison_two_ball_of_local_comparison_and_dimH
#print axioms fourPointComparison_two_ball_of_intrinsic_local_comparison_and_dimH
```
