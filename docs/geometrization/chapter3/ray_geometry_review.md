# Compiled self-review: geometry outside a supplied ray

Four public theorems in three leaves add six owned declarations, including
generated proof declarations. The 228-module gate checks 1142 owned
declarations (3062 jobs), including their transitive axiom closures; only
propext, Classical.choice and Quot.sound occur. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were checked
manually; defLemma is unavailable. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning remains outside these closures.
Static audit passes. No full migrated root, fresh blueprint PDF/Overleaf
build, human or delegated review is claimed.

The compiled review obtains openness of actual real segment interiors from
the accepted dimension-one theorem. It checks a closed ball of radius2 in
the segment[-2,3], including the boundary, and every positive radius on the
actual nonnegative real ray. For all negative real x and nonnegative t it
checks the exact exterior-ray distance formula, including t=0. The
common-opposite theorem is applied at arbitrary kappa>=0 on the actual
restricted set[-5,1] to p=0,x=-3,y=-5,z=1; separate examples cover x=p and
y=p. The driver exits zero with only four axiom reports.

The statement audit checks that segment openness is explicit, closed-ball
density is derived from actual segments, and ambient completeness is not
introduced. The exterior point is excluded from the entire ray range,
not merely an initial subsegment. The common opposite is the same z in
both equalities and z!=p is retained. Its four-point condition is restricted
to the supplied set, with all four memberships explicit. It works for any
nonnegative curvature parameter through the actual model-side identity.
These are geometric consequences of supplied rays; ray existence and
global line/ray/circle classification are not premises disguised as proofs
and are not claimed as conclusions here.

```lean
import DifferentialGeometry.Topology.MetricSpace.RayExteriorDistance
import DifferentialGeometry.Geometry.Comparison.CommonOpposite
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
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

private theorem real_open_segments (a b : ℝ) (σ : Icc a b → ℝ) (hσ : Isometry σ) :
    IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
  apply isOpen_segment_image_of_dimH_le_one real_curves (real_comparison (by norm_num))
    (fun z => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
  simpa only [Real.dimH_univ] using (le_refl (1 : ENNReal))
  exact hσ

private def real_ray : Ici (0 : ℝ) → ℝ := Subtype.val
private theorem real_ray_isometry : Isometry real_ray :=
  Isometry.of_dist_eq (fun _ _ => rfl)

example : closedBall (0 : ℝ) 2 =
    (fun t : Icc (-2 : ℝ) 3 => (t : ℝ)) '' {t | dist t (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 3) ≤ 2} := by
  exact closedBall_eq_segment_image_of_isOpen real_segments
    (Isometry.of_dist_eq (fun _ _ => rfl))
    (real_open_segments (-2) 3 _ (Isometry.of_dist_eq (fun _ _ => rfl)))
    ⟨0, by norm_num⟩ (by norm_num) (by norm_num)

example {R : ℝ} (hR : 0 < R) :
    closedBall R R = real_ray '' {t | (t : ℝ) ≤ 2 * R} :=
  closedBall_on_isometric_ray_of_isOpen_segments real_segments real_open_segments real_ray_isometry hR

example {x : ℝ} (hx : x < 0) (t : Ici (0 : ℝ)) : dist x (t : ℝ) = -x + (t : ℝ) := by
  have hnot : x ∉ range real_ray := by
    rintro ⟨s, hs⟩
    have hs0 : 0 ≤ (s : ℝ) := s.property
    change (s : ℝ) = x at hs
    linarith
  have h := dist_to_isometric_ray_of_not_mem_range real_segments real_open_segments
    real_ray_isometry hnot t
  simpa only [real_ray, Real.dist_eq x 0, sub_zero, abs_of_neg hx] using h

example {κ : ℝ} (hκ : 0 ≤ κ) :
    dist (-3 : ℝ) (-5) = |dist (-3 : ℝ) 0 - dist (-5 : ℝ) 0| := by
  apply dist_eq_abs_sub_of_common_opposite hκ
    ((real_comparison hκ).mono (subset_univ (Icc (-5 : ℝ) 1)))
    (p := 0) (z := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [Real.dist_eq]

example {κ : ℝ} (hκ : 0 ≤ κ) : dist (0 : ℝ) (-5) = |dist (0 : ℝ) 0 - dist (-5 : ℝ) 0| := by
  apply dist_eq_abs_sub_of_common_opposite hκ (real_comparison hκ)
    (p := 0) (z := 1) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (by norm_num)
  all_goals norm_num [Real.dist_eq]

example {κ : ℝ} (hκ : 0 ≤ κ) : dist (-3 : ℝ) 0 = |dist (-3 : ℝ) 0 - dist (0 : ℝ) 0| := by
  apply dist_eq_abs_sub_of_common_opposite hκ (real_comparison hκ)
    (p := 0) (z := 1) (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) (by norm_num)
  all_goals norm_num [Real.dist_eq]

#print axioms Metric.closedBall_eq_segment_image_of_isOpen
#print axioms Metric.closedBall_on_isometric_ray_of_isOpen_segments
#print axioms Metric.dist_to_isometric_ray_of_not_mem_range
#print axioms dist_eq_abs_sub_of_common_opposite
```
