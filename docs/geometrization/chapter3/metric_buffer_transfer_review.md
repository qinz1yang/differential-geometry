# Compiled self-review: metric buffer transfer

Eleven public theorems and two generated declarations add13 owned declarations.
The188-module gate passes for994 owned declarations, with only propext,
Classical.choice and Quot.sound in all new transitive axiom closures.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable and declaration kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no full migrated root,
PDF or Overleaf build is claimed.

The compiled driver realizes Y as the open real interval(-256,256), using
its actual subtype embedding into the complete real line. Y is incomplete;
no CompleteSpace instance on Y is used. Actual linear segments supply its
length property, and bounded local neighborhoods supply local comparison.
The new transfer proves its closed200-ball complete and endpoint comparison
at radius10, then proves ambient four-point comparison on the radius1-ball.
A separate example transfers a local neighborhood through the open embedding.
Another preserves the canonical angle of arbitrary supplied real germs under
reflection; it assumes neither radiality nor special values at zero.
Initial driver-only naming/API errors were corrected; the script below
compiled with exit zero.

Statement audit: completeness transfer uses Cauchy filters and the explicit
image margin, with a topological embedding and only a forward nonexpansive
bound. It assumes neither global isometry nor a uniformly continuous inverse.
The conditional assembly retains actual curve-length, local compactness,
local comparison and inner pairwise metric-identification hypotheses. It
proves the inner-ball image equality; it does not assume it. The actual
intrinsic metric and ALG06's remaining radial conclusions are not claimed
constructed. This is self-review, not independent human/delegated review.

```lean
import DifferentialGeometry.Geometry.Comparison.AmbientBufferComparison
import Mathlib.Analysis.Normed.Module.Convex
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic

open Set Metric Filter Topology
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


local instance : LocallyCompactSpace (ball (0 : ℝ) 256) := isOpen_ball.locallyCompactSpace

private def interval_base : ball (0 : ℝ) 256 := ⟨0, by norm_num [mem_ball]⟩

private theorem interval_segments (x y : ball (0 : ℝ) 256) :
    ∃ f : unitInterval → ball (0 : ℝ) 256, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ball (0 : ℝ) 256 := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      exact (convex_ball (0 : ℝ) 256) x.property y.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩
  have hd (s t : unitInterval) : dist (f s) (f t) = dist x y * dist s t := by
    change |(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ))| =
      |(x : ℝ) - y| * |(s : ℝ) - t|
    rw [show (1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ)) =
      ((y : ℝ) - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm (y : ℝ) x]
  have hLip : LipschitzWith (nndist x y) f :=
    LipschitzWith.of_dist_le_mul (fun s t => (hd s t).le)
  refine ⟨f, hLip.continuous, ?_, ?_, hd⟩
  · apply Subtype.ext
    simp [f]
  · apply Subtype.ext
    simp [f]

private theorem interval_curves : ∀ a b : ball (0 : ℝ) 256, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ball (0 : ℝ) 256, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments interval_segments

private theorem interval_local {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ z : ball (0 : ℝ) 256, ∃ Ω : Set (ball (0 : ℝ) 256),
      IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  intro z
  refine ⟨ball z 1, isOpen_ball, ?_, by simp⟩
  intro x hx a ha b hb c hc hax hbx hcx
  exact real_comparison hκ (x : ℝ) (mem_univ _) a (mem_univ _) b (mem_univ _)
    c (mem_univ _) (fun h => hax (Subtype.ext h))
    (fun h => hbx (Subtype.ext h)) (fun h => hcx (Subtype.ext h))

example : IsComplete (closedBall interval_base 200) := by
  have h := IsEmbedding.subtypeVal.isComplete_closedBall_of_256_radius_buffer
    isometry_subtype_coe.lipschitzWith (R := (1 : ℝ)) (by norm_num)
    (by simpa only [mul_one] using (Subtype.range_val (s := ball (0 : ℝ) 256)))
    (p := interval_base) (by norm_num [interval_base, mem_ball])
  simpa only [mul_one] using h

example : endpointHingeComparison 2 interval_base 10 := by
  have h := endpointHingeComparison_of_embedded_256_buffer (κ := 2) (R := 1)
    (by norm_num) (by norm_num) IsEmbedding.subtypeVal isometry_subtype_coe.lipschitzWith
    (by simpa only [mul_one] using (Subtype.range_val (s := ball (0 : ℝ) 256)))
    interval_curves (interval_local (by norm_num)) (p := interval_base)
    (by norm_num [interval_base, mem_ball])
  simpa only [mul_one] using h

example : fourPointComparison 2 (ball (0 : ℝ) 1) := by
  exact fourPointComparison_of_embedded_256_buffer (κ := 2) (R := 1)
    (by norm_num) (by norm_num) IsEmbedding.subtypeVal isometry_subtype_coe.lipschitzWith
    (by simpa only [mul_one] using (Subtype.range_val (s := ball (0 : ℝ) 256)))
    interval_curves (interval_local (by norm_num)) (p := interval_base) rfl
    (fun _ _ _ _ => rfl)

example : ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison 2 Ω ∧ (0 : ℝ) ∈ Ω := by
  exact exists_local_fourPointComparison_image
    (f := fun y : ball (0 : ℝ) 256 => (y : ℝ)) (p := interval_base)
    isOpen_ball.isOpenEmbedding_subtypeVal
    (interval_local (by norm_num) interval_base) ⟨1, by norm_num, fun _ _ _ _ => rfl⟩

example (γ β : ℝ → ℝ) :
    germComparisonAngle 2 ((fun x : ℝ => -x) ∘ γ) ((fun x : ℝ => -x) ∘ β) =
      germComparisonAngle 2 γ β := by
  exact germComparisonAngle_comp_of_dist_eq_on (R := 2) (S := 3)
    (by norm_num) (by norm_num) (fun _ _ _ _ => dist_neg_neg _ _)

#print axioms IsEmbedding.isComplete_closedBall_of_nonexpansive
#print axioms fourPointComparison_image_iff_of_dist_eq
#print axioms germComparisonAngle_comp_of_dist_eq_on
#print axioms fourPointComparison_of_endpoint_hinges
#print axioms endpointHingeComparison_of_embedded_256_buffer
#print axioms fourPointComparison_of_embedded_256_buffer
```
