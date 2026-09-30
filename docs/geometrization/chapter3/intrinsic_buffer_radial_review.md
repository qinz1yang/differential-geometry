# Compiled self-review: full ALG06 intrinsic and radial assembly

Thirteen public theorems and three generated declarations in four leaves add16
owned declarations. The201-module gate passes for1058 owned declarations
(3035 build jobs). New transitive axiom closures contain only propext,
Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF and
synTaut linters are silent; defLemma is unavailable, and kinds were inspected
manually. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes;
no full migrated root, PDF, Overleaf, human or delegated review is claimed.

The review constructs the actual intrinsic metric of the real open256-ball.
Its distance equality is separately proved from actual linear paths and the
path infimum, then used to give bounded LOCAL comparison neighborhoods in
that actual metric. This avoids accidentally supplying local comparison for
the original subtype metric. All generated topology and metric parents are
explicit. From that input, the new assembly proves ambient2-ball comparison
for kappa2 and ambient1-ball comparison for kappa0; it also proves actual
intrinsic endpoint comparison at the off-center point3 with radius10.
No CompleteSpace instance on the open domain is supplied.

Further examples check point-on-side comparison with endpoints1,-1 on the
CLOSED unit ball and intermediate point1/2, and with zero subsegment at0.
The same opposite real rays supply independent two-arm monotonicity, retaining
their original maps. Actual minimizing-path existence to the closed-boundary
point1 is tested with only local compactness of the larger open ball.
The public generic point-on-side result permits any four points in the2R
ball, so it also covers radial subtriangles whose intermediate endpoints
need not remain in the closedR-ball. The containment lemma and generic
monotonicity theorem retain all choices of the supplied minimizing paths.

The statement/dependency audit checks the exact256R/200R/10R margins and
81*(2R)<=200R. The extra2R four-point conclusion is derived from the actual
proved buffer theorem, not an unverified strengthening of a cited result.
AC13 supplies local distance equality on the same points, so no path-replacement
or assumed global intrinsic isometry enters the general result. Local
compactness and local curvature are explicit; finite dimension and global
source properness are not silently introduced. ALG06 is now fully assembled
in the written256R scope; AC02's separate8R scope and downstream uniform
covering and global recognition remain separate.

```lean
import DifferentialGeometry.Geometry.Comparison.IntrinsicRadialComparison
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

private theorem actual_local {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ z : ball (0 : ℝ) (256 * (1 : ℝ)), ∃ Ω : Set (ball (0 : ℝ) (256 * (1 : ℝ))),
      @IsOpen _ actualMetric.toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ actualMetric κ Ω ∧ z ∈ Ω := by
  intro z
  refine ⟨ball z 1, ?_, ?_, by simp⟩
  · change @IsOpen _ (intrinsicBallMetricSpace real_curves 0 (by norm_num)).toUniformSpace.toTopologicalSpace _
    rw [intrinsicBallMetricSpace_toTopology]
    exact isOpen_ball
  · apply (@fourPointComparison_image_iff_of_dist_eq ℝ
      (ball (0 : ℝ) (256 * (1 : ℝ))) _ actualMetric κ Subtype.val (ball z 1)
      (fun a _ b _ => (actual_dist a b).symm)).mp
    exact (real_comparison hκ).mono (subset_univ _)

example : fourPointComparison 2 (ball (0 : ℝ) (2 * 1)) :=
  fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num) (actual_local (by norm_num))

example : fourPointComparison 0 (ball (0 : ℝ) 1) :=
  fourPointComparison_ambient_ball_of_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num) (actual_local (by norm_num))

example : @endpointHingeComparison _ actualMetric 2
    ⟨3, by norm_num [mem_ball, Real.dist_eq]⟩ (10 * 1) :=
  endpointHingeComparison_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num) (actual_local (by norm_num))
    (by norm_num [mem_ball, Real.dist_eq])

example : modelSideNegCurvature 2 (dist (0 : ℝ) (1/2)) (dist (0 : ℝ) (-1))
    (comparisonAngleNegCurvature 2 (dist (0 : ℝ) 1) (dist (0 : ℝ) (-1))
      (dist (1 : ℝ) (-1))) ≤ dist (1/2 : ℝ) (-1) := by
  exact radial_point_on_side_of_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (actual_local (by norm_num))
    (by norm_num [mem_ball]) (by norm_num [mem_closedBall, Real.dist_eq])
    (by norm_num [mem_closedBall, Real.dist_eq]) (by norm_num [Real.dist_eq])

example : modelSideNegCurvature 2 (dist (0 : ℝ) 0) (dist (0 : ℝ) (-1))
    (comparisonAngleNegCurvature 2 (dist (0 : ℝ) 1) (dist (0 : ℝ) (-1))
      (dist (1 : ℝ) (-1))) ≤ dist (0 : ℝ) (-1) := by
  exact radial_point_on_side_of_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (actual_local (by norm_num))
    (by norm_num [mem_ball]) (by norm_num [mem_closedBall, Real.dist_eq])
    (by norm_num [mem_closedBall, Real.dist_eq]) (by norm_num [Real.dist_eq])

example : DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn 1 1
    (fun s t => comparisonAngleNegCurvature 2 s t (dist s (-t))) := by
  apply independent_radial_monotonicity_of_intrinsic_256_buffer real_curves 0
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (actual_local (by norm_num))
    (q := 0) (γ := fun s => s) (β := fun t => -t)
  · norm_num [mem_ball]
  · norm_num [mem_closedBall, Real.dist_eq]
  · norm_num [mem_closedBall, Real.dist_eq]
  · intro s hs
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs.1]
  · intro t ht
    simp only [Real.dist_eq, sub_neg_eq_add, zero_add, abs_of_pos ht.1]
  · intro s hs t ht
    rfl
  · intro s hs t ht
    exact dist_neg_neg s t

example : ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = 0 ∧ f 1 = 1 ∧
    (∀ t, f t ∈ ball 0 (2 * 1)) ∧
    ∀ s t, dist (f s) (f t) = dist (0 : ℝ) 1 * dist s t :=
  exists_radial_metric_segment_in_two_ball real_curves 0 (L := 256 * 1)
    (by norm_num) (by norm_num) (by norm_num [mem_ball])
    (by norm_num [mem_closedBall, Real.dist_eq])

#print axioms intrinsicBall_dist_eq_on_inner_closedBall
#print axioms intrinsicBall_ball_image
#print axioms intrinsicBallMetricSpace_locallyCompact
#print axioms endpointHingeComparison_intrinsic_256_buffer
#print axioms fourPointComparison_intrinsic_two_ball_of_256_buffer
#print axioms fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer
#print axioms fourPointComparison_ambient_ball_of_intrinsic_256_buffer
#print axioms exists_radial_metric_segment_in_two_ball
#print axioms radial_point_on_side_of_intrinsic_256_buffer
#print axioms independent_radial_monotonicity_of_intrinsic_256_buffer
```
