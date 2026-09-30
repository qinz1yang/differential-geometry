# Compiled self-review: AC03 exact radial contraction

Four public theorems and seven generated declarations in two leaves add11
owned declarations. The206-module gate passes for1074 declarations (3040
build jobs). New transitive axiom closures contain only propext, Classical.choice
and Quot.sound. Source-copy unusedArguments, simpNF and synTaut linters are
silent; declaration kinds were manually inspected because defLemma is
unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes;
no full migrated root, PDF, Overleaf, human or delegated review is claimed.

The compiled review checks the literal chosen real segments f(x,s)=s*x on
the CLOSED unit ball, with delta1/2 and fraction1/4. It obtains the exact
half-over-sinh2 lower coefficient for all pairs, including the center and
repeated endpoints. A separate consumer constructs its own contraction from
original bounded local ambient comparison neighborhoods in the256-ball.
Two explicit finite-configuration examples exercise the left-zero-arm and
right-zero-arm branches, rather than using an assumed positive-arm theorem.

Statement review checks all quantifiers: every supplied family of minimizing
segments works; no continuity in the endpoint variable is assumed or claimed.
The exact fraction is supplied with its real-value identity. Its radial
subpoints remain in the same2R domain, and the final map lies strictly inside
the delta-ball. The lower coefficient is exactly delta/sinh(2R). The existence
consumer constructs actual segments, with local compactness confined to the
specified open buffer. It does not assume global properness or global
geodesicity. The written256R route remains distinct from the sharp8R/KL input.

BBI370/PDF385 was also rendered and visually inspected for the source formula.
Its printed general-curvature -k scaling is not imported as a theorem for
arbitrary k. The implementation uses k=-1 and the independently checked scalar
cosine-law proof; retained errata evidence and that normalization distinction
are recorded in the source manifest. AC04's exact chart/net assembly remains.

```lean
import DifferentialGeometry.Geometry.Comparison.RadialContraction
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

local instance : LocallyCompactSpace (ball (0 : ℝ) (256 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

private noncomputable def quarter : unitInterval := ⟨1/4, by norm_num⟩

private noncomputable def chosen (x : closedBall (0 : ℝ) 1) (s : unitInterval) : ℝ :=
  (s : ℝ) * (x : ℝ)

private theorem chosen_dist (x : closedBall (0 : ℝ) 1) (s t : unitInterval) :
    dist (chosen x s) (chosen x t) = dist (0 : ℝ) (x : ℝ) * dist s t := by
  change |(s : ℝ) * (x : ℝ) - (t : ℝ) * (x : ℝ)| =
    |0 - (x : ℝ)| * |(s : ℝ) - t|
  rw [show (s : ℝ) * (x : ℝ) - (t : ℝ) * (x : ℝ) =
    (x : ℝ) * ((s : ℝ) - t) by ring, abs_mul, zero_sub, abs_neg]

example : (∀ x, chosen x quarter ∈ ball (0 : ℝ) (1/2)) ∧
    ∀ x y : closedBall (0 : ℝ) 1,
      ((1/2) / Real.sinh (2 * 1)) * dist (x : ℝ) (y : ℝ) ≤
        dist (chosen x quarter) (chosen y quarter) := by
  apply radial_contraction_of_chosen_metric_segments
    ((real_comparison (by norm_num : (0 : ℝ) ≤ 1)).mono (subset_univ _))
    (by norm_num [mem_ball]) (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1) quarter
    (by norm_num [quarter]) chosen
  · intro x
    simp [chosen]
  · intro x
    simp [chosen]
  · exact chosen_dist

example : ∃ h : closedBall (0 : ℝ) 1 → ℝ,
    (∀ x, h x ∈ ball 0 (1/2)) ∧
    ∀ x y : closedBall (0 : ℝ) 1,
      ((1/2) / Real.sinh (2 * 1)) * dist (x : ℝ) (y : ℝ) ≤ dist (h x) (h y) := by
  exact exists_radial_contraction_of_local_256_buffer real_curves 0
    (by norm_num) (fun z _ => ambient_local z (by norm_num))
    (by norm_num [mem_ball]) (by norm_num)

example : (((1/4 : ℝ) * 2) / Real.sinh 2) * dist (0 : ℝ) 1 ≤ dist (0 : ℝ) (1/4) := by
  exact dist_radial_points_lower_including_zero_arms (real_comparison (by norm_num))
    (q := 0) (x := 0) (y := 1) (u := 0) (v := 1/4)
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])

example : (((1/4 : ℝ) * 2) / Real.sinh 2) * dist (1 : ℝ) 0 ≤ dist (1/4 : ℝ) 0 := by
  exact dist_radial_points_lower_including_zero_arms (real_comparison (by norm_num))
    (q := 0) (x := 1) (y := 0) (u := 1/4) (v := 0)
    (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _)
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])

#print axioms dist_radial_points_lower_including_zero_arms
#print axioms radial_contraction_of_chosen_metric_segments
#print axioms exists_radial_contraction_of_comparison_buffer
#print axioms exists_radial_contraction_of_local_256_buffer
```
