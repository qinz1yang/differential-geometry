# Compiled self-review: fixed-curvature dimension-to-covering producer

Three public theorems and five generated declarations in two leaves add eight
owned declarations. The213-module gate passes for1100 declarations (3047
build jobs), with only propext, Classical.choice and Quot.sound in new
transitive axiom closures. Source-copy unusedArguments, simpNF and synTaut
linters are silent; defLemma is unavailable and kinds were inspected manually.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier
warning is outside these closures. Static audit passes; no full migrated
root, PDF, Overleaf, human or delegated review is claimed.

The compiled review applies the complete producer to the real line with
only local comparison, actual length curves and dimH(real)=1. For every
positive epsilon it obtains the literal fixed1 ceiling bound and strict
internal coverage of the closed unit ball, without supplying a chart or
local compactness. Both the ambient and explicitly constructed intrinsic
local-comparison input versions are exercised. A concrete one-point subtype
of the real line tests the singleton branch with dimension bound3, actual
constant length curves and vacuous four-point comparison. A separate1-to3
rank check verifies the numerical monotonicity used to keep the final bound
independent of chart rank. Review-only inference/numeral-cast issues were
resolved by explicit parameters and small cast rewrites; no heartbeat limit
was raised. Final review compiled with exit zero and only axiom reports.

Statement audit checks original ambient completeness and dimension, the
exact256R region, n>=1, and the fixed distortion L_n. The nontrivial proof
actually derives local compactness, chooses the nearby distance-coordinate
chart, constructs radial contraction, bounds finite packing and applies
greedy nets. The singleton uses the actual basepoint singleton. Neither
branch adds global source properness or a uniform chart radius. The final
constant uses n even if the constructed chart has rank m<n; monotonicity
is proved with bases at least1 and nonnegative hyperbolic coefficient.
The intrinsic consumer's curvature premise names the actual generated metric
and topology. Varying-curvature normalization and growing-region SAME-limit
assembly remain explicit future work.

```lean
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

example (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset ℝ,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sinh 2 / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, ∃ y ∈ T, dist x y < ε := by
  have hdim : dimH (ball (0 : ℝ) (256 * 1)) ≤ (1 : ℕ) := by
    simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (ball (0 : ℝ) (256 * 1)))).trans_eq Real.dimH_univ
  have h := exists_closedBall_net_of_local_comparison_and_dimH real_curves 0
    (by norm_num : (0 : ℝ) < 1) hε (by omega : 1 ≤ (1 : ℕ)) hdim
    (fun z _ => ambient_local z (by norm_num))
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

example (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset ℝ,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sinh 2 / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, ∃ y ∈ T, dist x y < ε := by
  have hdim : dimH (ball (0 : ℝ) (256 * 1)) ≤ (1 : ℕ) := by
    simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (ball (0 : ℝ) (256 * 1)))).trans_eq Real.dimH_univ
  have h := exists_closedBall_net_of_intrinsic_local_comparison_and_dimH real_curves 0
    (by norm_num : (0 : ℝ) < 1) hε (by omega : 1 ≤ (1 : ℕ)) hdim
    (fun z => (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
      (by norm_num : (0 : ℝ) < 256 * 1) z).mpr (ambient_local z (by norm_num)))
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

private abbrev OnePoint := {x : ℝ // x = 0}

local instance : Subsingleton OnePoint :=
  ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩

local instance : CompleteSpace OnePoint :=
  (isClosed_eq continuous_id continuous_const).completeSpace_coe

private def one_base : OnePoint := ⟨0, rfl⟩

private theorem one_curves : ∀ x y : OnePoint, ∀ η : ℝ, 0 < η →
    ∃ c : unitInterval → OnePoint, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + η) := by
  intro x y η hη
  refine ⟨fun _ => x, continuous_const, rfl, Subsingleton.elim _ _, ?_⟩
  have hz : eVariationOn (fun _ : unitInterval => x) univ = 0 :=
    (eVariationOn.eq_zero_iff _).mpr (fun _ _ _ _ => edist_self _)
  rw [hz]
  exact ENNReal.ofReal_pos.mpr (by linarith [dist_nonneg (x := x) (y := y)])

example (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset OnePoint,
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion 3) ^ 2 * Real.sqrt 3 * Real.sinh (2 * 1) / ε⌉₊) ^ 3 ∧
      (T : Set OnePoint) ⊆ closedBall one_base 1 ∧
      ∀ x ∈ closedBall one_base 1, ∃ y ∈ T, dist x y < ε := by
  apply exists_closedBall_net_of_local_comparison_and_dimH one_curves one_base
    (by norm_num) hε (by omega : 1 ≤ (3 : ℕ))
  · rw [dimH_subsingleton (show (ball one_base (256 * 1)).Subsingleton from
      fun _ _ _ _ => Subsingleton.elim _ _)]
    exact bot_le
  · intro p hp
    refine ⟨univ, isOpen_univ, ?_, mem_univ _⟩
    intro x hx a ha b hb c hc hax hbx hcx
    exact (hax (Subsingleton.elim _ _)).elim

example {L ε : ℝ} (hε : 0 < ε) :
    (1 + ⌈4 * L ^ 2 * Real.sqrt 1 * Real.sinh (2 * 1) / ε⌉₊) ^ 1 ≤
      (1 + ⌈4 * L ^ 2 * Real.sqrt 3 * Real.sinh (2 * 1) / ε⌉₊) ^ 3 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (chart_net_bound_mono_dimension (m := 1) (n := 3) (L := L) (R := 1)
      (by omega) (by norm_num) hε)

#print axioms chart_net_bound_mono_dimension
#print axioms exists_closedBall_net_of_local_comparison_and_dimH
#print axioms exists_closedBall_net_of_intrinsic_local_comparison_and_dimH
```
