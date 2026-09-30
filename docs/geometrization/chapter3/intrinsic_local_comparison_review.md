# Compiled self-review: local ambient/intrinsic comparison

Four public theorems and one generated declaration in three leaves add five
owned declarations. The204-module gate passes for1063 declarations (3038
build jobs); all new transitive closures contain only propext, Classical.choice
and Quot.sound. Source-copy unusedArguments, simpNF and synTaut linters are
silent; defLemma is unavailable and kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no full migrated root,
PDF, Overleaf, human or delegated review is claimed.

The actual real open256-ball metric is constructed from path infima. Bounded
AMBIENT comparison neighborhoods at arbitrary points are transferred into its
explicit intrinsic topology/metric and then back, testing both directions.
The source-facing consumer derives ambient2-ball comparison at kappa2 and0
without supplying intrinsic local comparison as input. A separate pullback
example uses x -> |x| near1: this map is not globally injective, while its
pairwise metric equality on the half-radius neighborhood suffices. Thus the
generic pullback theorem does not hide a global embedding requirement.

The statement audit checks each topology and metric parent explicitly,
including the local comparison hypothesis and conclusion. The common radius
is positive because the point belongs to the open L-ball. Nonexpansion
puts the intrinsic radius-r neighborhood inside the ambient one; AC13's4r
margin then gives equality for EVERY pair in that neighborhood. Completeness,
local compactness and sign of kappa are absent from the local equivalence;
only the later ALG06 consumer requires completeness, local compactness and
kappa>=0. Neighborhoods vary with the point. This closes the local-transfer
input, not full ALG07's covering and extraction route.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalBufferComparison
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

private theorem interval_segments (x y : ball (0 : ℝ) (256 * (1 : ℝ))) :
    ∃ f : unitInterval → ball (0 : ℝ) (256 * (1 : ℝ)), Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ball (0 : ℝ) (256 * (1 : ℝ)) := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      exact (convex_ball (0 : ℝ) (256 * (1 : ℝ))) x.property y.property
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

private theorem interval_curves : ∀ a b : ball (0 : ℝ) (256 * (1 : ℝ)), ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ball (0 : ℝ) (256 * (1 : ℝ)), Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments interval_segments

local instance : LocallyCompactSpace (ball (0 : ℝ) (256 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

@[instance_reducible]
private noncomputable def actualMetric : MetricSpace (ball (0 : ℝ) (256 * (1 : ℝ))) :=
  intrinsicBallMetricSpace real_curves 0 (by norm_num)

private theorem actual_dist (a b : ball (0 : ℝ) (256 * (1 : ℝ))) :
    @dist _ actualMetric.toDist a b = dist (a : ℝ) (b : ℝ) := by
  rw [show @dist _ actualMetric.toDist a b = (intrinsicEDist a b).toReal from rfl,
    intrinsicEDist_eq_edist_of_arbitrarily_short_curves interval_curves,
    edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rfl

private theorem ambient_local (z : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  refine ⟨Ioo (z - 1) (z + 1), isOpen_Ioo,
    (real_comparison hκ).mono (subset_univ _), ?_⟩
  exact ⟨by linarith, by linarith⟩

private theorem actual_local {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ z : ball (0 : ℝ) (256 * (1 : ℝ)), ∃ Ω : Set (ball (0 : ℝ) (256 * (1 : ℝ))),
      @IsOpen _ actualMetric.toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ actualMetric κ Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
    (by norm_num) z).mpr (ambient_local z hκ)

example (z : ball (0 : ℝ) (256 * (1 : ℝ))) :
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison 2 Ω ∧ (z : ℝ) ∈ Ω :=
  (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
    (by norm_num) z).mp (actual_local (by norm_num) z)

example : fourPointComparison 2 (ball (0 : ℝ) (2 * 1)) :=
  fourPointComparison_two_ball_of_local_256_buffer real_curves 0
    (by norm_num) (by norm_num) (fun z _ => ambient_local z (by norm_num))

example : fourPointComparison 0 (ball (0 : ℝ) (2 * 1)) :=
  fourPointComparison_two_ball_of_local_256_buffer real_curves 0
    (by norm_num) (by norm_num) (fun z _ => ambient_local z (by norm_num))

example : ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison 2 Ω ∧ (1 : ℝ) ∈ Ω := by
  apply exists_local_fourPointComparison_preimage (f := fun x : ℝ => |x|)
    continuous_abs (ambient_local |(1 : ℝ)| (by norm_num))
  refine ⟨1/2, by norm_num, ?_⟩
  intro a ha b hb
  have hapos : 0 ≤ a := by
    have h := abs_lt.mp (show |a - 1| < 1/2 from ha)
    linarith
  have hbpos : 0 ≤ b := by
    have h := abs_lt.mp (show |b - 1| < 1/2 from hb)
    linarith
  rw [abs_of_nonneg hapos, abs_of_nonneg hbpos]

#print axioms exists_local_fourPointComparison_preimage
#print axioms exists_local_fourPointComparison_iff_of_isOpenEmbedding
#print axioms exists_local_fourPointComparison_intrinsicBall_iff
#print axioms fourPointComparison_two_ball_of_local_256_buffer
```
