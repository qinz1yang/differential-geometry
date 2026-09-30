# Compiled self-review: all-point compactness and nearby charts

Six public theorems in three leaves add six owned declarations. The211-module
gate passes for1092 declarations (3045 build jobs), with only propext,
Classical.choice and Quot.sound in new transitive axiom closures. Source-copy
unusedArguments, simpNF and synTaut linters are silent; defLemma is unavailable
and declaration kinds were inspected manually. Earlier mathematical leaves
remain unchanged. The inherited AreaUpperBarrier warning is outside these
closures. Static audit passes; no full migrated root, PDF, Overleaf, human
or delegated review is claimed.

The compiled review proves local compactness of the real open8-ball both
from original local ambient comparison and from explicitly constructed
intrinsic local comparison. The original ambient dimension bound is obtained
from dimH(real)=1. A second test uses the actual intrinsic comparison input
to produce a centered chart in every prescribed positive epsilon-neighborhood,
then uses1<=m<=1 to obtain an actual one-dimensional map. Its domain remains
inside the original8-ball and that SAME epsilon-neighborhood, with both
bounds using the exact fixed pairedChartDistortion1. The zero-at-center
condition is retained. The universal distortion lower bound is checked too.

Statement audit checks that neither main local-structure producer assumes
local compactness, global properness, a chart, or a uniform radius. Ambient
completeness supplies actual closed completeness buffers. Intersections
preserve the local four-point and ambient dimension bounds. The compact
balls are contained in the original region, which is necessary for compact
preimage transport into its subtype. The metric R1 property upgrades compact
neighborhoods to the genuine locally compact typeclass. The rough-dimension
subsingleton/n=0 cases are inherited unchanged. The chart theorem explicitly
requires a nontrivial source and n>=1, retains its actual distance-coordinate
formula and anchors, and permits arbitrarily small positive epsilon.

The intrinsic consumers specify the constructed topology and metric parents;
no original subtype metric is silently used for their curvature premise.
They transport local comparison and then run the proved local constructions
in the original complete ambient space, so the output chart's distances
need no unproved reconstruction. This closes AC07/AC29's local-structure
producer scope; fixed-n net and growing-region extraction assembly remain.

```lean
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness
import DifferentialGeometry.Geometry.Comparison.NearbyPairedChart
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

@[instance_reducible]
private noncomputable def actualEightMetric : MetricSpace (ball (0 : ℝ) 8) :=
  intrinsicBallMetricSpace real_curves 0 (by norm_num)

private theorem eight_dim : dimH (ball (0 : ℝ) 8) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using (dimH_mono (subset_univ (ball (0 : ℝ) 8))).trans_eq Real.dimH_univ

private theorem actual_eight_local (p : ball (0 : ℝ) 8) :
    ∃ Ω : Set (ball (0 : ℝ) 8),
      @IsOpen _ actualEightMetric.toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ actualEightMetric 1 Ω ∧ p ∈ Ω :=
  (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
    (by norm_num) p).mpr (ambient_local p (by norm_num))

example : LocallyCompactSpace (ball (0 : ℝ) 8) :=
  locallyCompactSpace_of_local_comparison_and_dimH real_curves isOpen_ball eight_dim
    (fun p _ => ambient_local p (by norm_num))

example : LocallyCompactSpace (ball (0 : ℝ) 8) :=
  locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH real_curves 0
    (by norm_num) eight_dim actual_eight_local

example : 1 ≤ pairedChartDistortion 1 := one_le_pairedChartDistortion (by omega)

example (ε : ℝ) (hε : 0 < ε) :
    ∃ q ∈ ball (0 : ℝ) ε, ∃ r : ℝ, ∃ hr : 0 < r,
      ball q r ⊆ ball 0 8 ∩ ball 0 ε ∧
      ∃ φ : ball q r → PiLp 2 (fun _ : Fin 1 => ℝ),
        φ ⟨q, mem_ball_self hr⟩ = 0 ∧
        (∀ x y : ball q r, (pairedChartDistortion 1)⁻¹ * dist x y ≤ dist (φ x) (φ y)) ∧
        (∀ x y : ball q r, dist (φ x) (φ y) ≤ pairedChartDistortion 1 * dist x y) := by
  obtain ⟨m, hm1, hmn, q, hq, a, ha, r, hr, hsub, φ, he, hz, hlo, hhi⟩ :=
    exists_centered_chart_near_of_intrinsic_local_comparison real_curves 0
      (by norm_num : (0 : ℝ) < 8) hε (by omega : 1 ≤ (1 : ℕ)) eight_dim
      (actual_eight_local ⟨0, by norm_num [mem_ball]⟩)
  have hm : m = 1 := by omega
  subst m
  exact ⟨q, hq.2, r, hr, hsub, φ, hz, hlo, hhi⟩

#print axioms locallyCompactSpace_subtype_of_compact_closedBalls
#print axioms locallyCompactSpace_of_local_comparison_and_dimH
#print axioms locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH
#print axioms one_le_pairedChartDistortion
#print axioms exists_centered_chart_near_of_local_comparison
#print axioms exists_centered_chart_near_of_intrinsic_local_comparison
```
