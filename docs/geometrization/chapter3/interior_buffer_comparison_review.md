# Compiled self-review: complete interior buffer

Four public theorems and one generated declaration add five owned declarations.
The 183-module gate passes for 981 owned declarations, with only propext,
Classical.choice and Quot.sound in every new transitive axiom closure.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable and declaration kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no full migrated root,
PDF or Overleaf build is claimed.

The compiled driver uses the open positive real ray, an incomplete metric
space, with no CompleteSpace instance. Actual linear segments supply its
length property. Direct real-line comparison supplies bounded local
neighborhoods. The closed radius400 ball about1000 is proved complete by
identifying its image with the real interval[600,1400]. The endpoint theorem
then gives radius20 comparison. A hinge centered at990 with endpoints1000
and995 has arm sum15<20. A segment from995 to1005 is also produced inside
the radius20 ball about1001, using the recentered buffer. The driver below
compiled with exit zero; initial script-only subtype/coercion errors were
corrected before acceptance.

Statement audit: no global minimizing-join or global completeness premise
is present. The theorem uses actual curve variation and the specified complete
ball. The constant20 is verified by the written almost-minimum/recentering
arithmetic. Range preservation in arclength reparametrization follows by
working inside the controlled ball subtype. Degenerate arms are included
in model-side comparison and zero-length segment construction; positive-arm
angle comparison retains its required hypotheses. This is self-review, not
an independent human or delegated review. Intrinsic transfer remains separate.

```lean
import DifferentialGeometry.Geometry.Comparison.InteriorBufferComparison
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


local instance : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace

private theorem ray_segments (x y : Ioi (0 : ℝ)) :
    ∃ f : unitInterval → Ioi (0 : ℝ), Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → Ioi (0 : ℝ) := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      have hx := x.property
      have hy := y.property
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases ht : (t : ℝ) = 0
      · simp [ht]
      · have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
        exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hx.le)
          (mul_pos htp hy)⟩
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

private theorem ray_curves : ∀ a b : Ioi (0 : ℝ), ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → Ioi (0 : ℝ), Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments ray_segments

private theorem ray_local {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ z : Ioi (0 : ℝ), ∃ Ω : Set (Ioi (0 : ℝ)),
      IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  intro z
  refine ⟨ball z 1, isOpen_ball, ?_, by simp⟩
  intro x hx a ha b hb c hc hax hbx hcx
  exact real_comparison hκ (x : ℝ) (mem_univ _) a (mem_univ _) b (mem_univ _)
    c (mem_univ _) (fun h => hax (Subtype.ext h))
    (fun h => hbx (Subtype.ext h)) (fun h => hcx (Subtype.ext h))

private def ray_point (x : ℝ) (hx : 0 < x) : Ioi (0 : ℝ) := ⟨x, hx⟩

private theorem ray_buffer : IsComplete (closedBall (ray_point 1000 (by norm_num)) 400) := by
  apply (isComplete_image_iff isometry_subtype_coe.isUniformInducing).mp
  have heq : Subtype.val '' closedBall (ray_point 1000 (by norm_num)) 400 =
      Icc (600 : ℝ) 1400 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change |(y : ℝ) - 1000| ≤ 400 at hy
      have h := abs_le.mp hy
      constructor <;> linarith
    · intro hx
      refine ⟨⟨x, by change 0 < x; linarith [hx.1]⟩, ?_, rfl⟩
      change |x - 1000| ≤ 400
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
  rw [heq]
  exact isClosed_Icc.isComplete

example : endpointHingeComparison 2 (ray_point 1000 (by norm_num)) 20 := by
  have h := endpointHingeComparison_of_complete_interior_buffer (κ := 2)
    (by norm_num) ray_curves (ray_local (by norm_num)) ray_buffer
  norm_num at h
  exact h

example : ∃ H : MinimizingHinge (ray_point 1000 (by norm_num)) (ray_point 995 (by norm_num)),
    H.center = ray_point 990 (by norm_num) ∧
      dist (ray_point 1000 (by norm_num)) (ray_point 995 (by norm_num)) ≤ H.modelSide 2 := by
  obtain ⟨f, _, hf0, hf1, hfd⟩ := ray_segments (ray_point 990 (by norm_num)) (ray_point 1000 (by norm_num))
  obtain ⟨g, _, hg0, hg1, hgd⟩ := ray_segments (ray_point 990 (by norm_num)) (ray_point 995 (by norm_num))
  obtain ⟨η, hη, hη0, hη1⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := exists_isometric_segment_of_dist_eq_mul hg0 hg1 hgd
  let H : MinimizingHinge (ray_point 1000 (by norm_num)) (ray_point 995 (by norm_num)) :=
    ⟨ray_point 990 (by norm_num), η, σ, hη, hσ, hη0, hσ0, hη1, hσ1⟩
  refine ⟨H, rfl, H.modelSide_ge_dist_of_complete_interior_buffer
    (by norm_num) ray_curves (ray_local (by norm_num)) ray_buffer ?_⟩
  norm_num [H, ray_point, Subtype.dist_eq, Real.dist_eq]

example : ∃ σ : Icc (0 : ℝ) (dist (ray_point 995 (by norm_num)) (ray_point 1005 (by norm_num))) → Ioi (0 : ℝ),
    Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = ray_point 995 (by norm_num) ∧
    σ ⟨dist (ray_point 995 (by norm_num)) (ray_point 1005 (by norm_num)), ⟨dist_nonneg, le_rfl⟩⟩ =
      ray_point 1005 (by norm_num) ∧ ∀ t, σ t ∈ ball (ray_point 1001 (by norm_num)) 20 := by
  have h := exists_isometric_segment_in_ball_of_recentered_complete_buffer
    (p := ray_point 1001 (by norm_num)) (r := 10) ray_curves (by norm_num) ray_buffer
    (by norm_num [ray_point, Subtype.dist_eq, Real.dist_eq])
    (a := ray_point 995 (by norm_num)) (b := ray_point 1005 (by norm_num))
    (by norm_num [mem_ball, ray_point, Subtype.dist_eq, Real.dist_eq])
    (by norm_num [mem_ball, ray_point, Subtype.dist_eq, Real.dist_eq])
  simpa only [show 2 * (10 : ℝ) = 20 by norm_num] using h

#print axioms exists_isometric_segment_in_ball_of_recentered_complete_buffer
#print axioms MinimizingHinge.modelSide_ge_dist_of_complete_interior_buffer
#print axioms MinimizingHinge.comparisonAngle_le_of_complete_interior_buffer
#print axioms endpointHingeComparison_of_complete_interior_buffer
```
