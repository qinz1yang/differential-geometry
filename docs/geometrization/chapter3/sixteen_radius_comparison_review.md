# Original AC36 at16R independent acceptance

Eight public theorems in three leaves add11 owned declarations, including three generated declarations. The372-module gate checks1738 declarations in3207 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;16 reports cover all eight production declarations and eight concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root and an independent peer read all selection/comparison/intrinsic-transfer proofs. Root reread the actual pinned AKP key lemma, almost-minimum lemma and full globalization proof. The changed quantitative argument is explicitly recorded, with its new constants identified as project proof choices. It preserves the ORIGINAL16R contract and conclusion, rather than renaming the older256R conclusion. No finite-dimensional premise is needed by this adapted argument.

The selection regression uses the actual incomplete interval(-100,100), nonconstant radius1+abs(x-1) and initial point0. It proves the selected point MUST move from0 while retaining the exact displacement/radius inequality and all nearby-radius bounds. A separate theta0 test checks the allowed endpoint of the decay parameter.

The geometric regressions construct actual real short curves and the actual intrinsic metric ofU=(-16,16), proving its distance equality and local four-point hypotheses for every kappa>=0. Both the original intrinsic and ambient headline conclusions are invoked. An original vertex0.99 obtains the exact45/11 endpoint radius. Its actual complete closed intrinsic15-ball contains15.99 at EXACT distance15; the test proves that point lies outside radius15 around the origin. In contrast, U with its actual intrinsic metric is proved INCOMPLETE. A final original ambient configuration near both inner boundaries evaluates the returned inequality at nonzero kappa2. No complete-open-domain or hidden proper-source premise is introduced.

The source KL2D safeguard and original8R AC02/AC64 remain separate. This proof uses retained-budget selection, the accepted cradle enlargement, actual complete15R buffers and actual ambient/intrinsic distance transfer. The finite-dimensional source assumption is an unnecessary stronger original hypothesis, not a missing new proof input. Blueprint207 and migration interfaces remain unchanged; Chapters3–4 are not declared complete.

```lean
import DifferentialGeometry.Geometry.Comparison.IntrinsicSixteenBufferComparison
import DifferentialGeometry.Geometry.Comparison.LocalBufferComparison
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

set_option autoImplicit false

set_option autoImplicit false
open Set Metric Filter Topology

namespace GCBudgetSelectionReview

abbrev X := ball (0 : ℝ) 100

def o : X := ⟨0, by norm_num⟩
def q : X := ⟨1, by norm_num [mem_ball, Real.dist_eq]⟩
noncomputable def radius (x : X) : ℝ := 1 + |(x : ℝ) - 1|

/-- The budget theorem must actually move the basepoint in this nonconstant example. -/
theorem exists_moved_almost_minimum :
    ∃ p : X, p ≠ o ∧
      (3 / 10 : ℝ) * dist p o + (11 / 10 : ℝ) * radius p ≤ 11 / 5 ∧
      radius p ≤ 2 ∧
      ∀ y : X, dist p y ≤ (11 / 10 : ℝ) * radius p →
        (7 / 10 : ℝ) * radius p < radius y := by
  have hc : IsComplete (closedBall o ((11 / 10 : ℝ) * radius o / (1 - 7 / 10))) := by
    apply Topology.IsEmbedding.subtypeVal.isComplete_closedBall_of_range_ball
      isometry_subtype_coe.lipschitzWith Subtype.range_val
    norm_num [o, radius]
  have hp (x : X) : 0 < radius x := by dsimp [radius]; positivity
  have hl : ∀ x ∈ closedBall o ((11 / 10 : ℝ) * radius o / (1 - 7 / 10)),
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ y in 𝓝 x, c ≤ radius y := by
    intro x hx
    refine ⟨1, by norm_num, Eventually.of_forall fun y => ?_⟩
    exact le_add_of_nonneg_right (abs_nonneg _)
  obtain ⟨p, hbudget, hrad, hnear⟩ := exists_relative_almost_minimum_with_budget
    (r := radius) (o := o) (a := (11 / 10 : ℝ)) (θ := (7 / 10 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hp hc hl
  have hpne : p ≠ o := by
    intro h
    subst p
    have hm := hnear q (by norm_num [o, q, radius, Subtype.dist_eq, Real.dist_eq])
    norm_num [o, q, radius] at hm
  refine ⟨p, hpne, ?_, ?_, hnear⟩
  · norm_num [radius, o] at hbudget ⊢
    exact hbudget
  · norm_num [radius, o] at hrad ⊢
    exact hrad

/-- The allowed endpoint `θ = 0` does not create a division-by-zero side condition. -/
theorem zero_decay_parameter :
    ∃ p : ℝ, dist p 0 + 1 ≤ 1 ∧
      ∀ q : ℝ, dist p q ≤ 1 → 0 < (1 : ℝ) := by
  obtain ⟨p, hb, _, hn⟩ := exists_relative_almost_minimum_with_budget
    (r := fun _ : ℝ => (1 : ℝ)) (o := 0) (a := (1 : ℝ)) (θ := (0 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)
    isClosed_closedBall.isComplete
    (fun x _ => ⟨1, by norm_num, Eventually.of_forall fun _ => le_rfl⟩)
  exact ⟨p, by simpa using hb, by simp⟩

end GCBudgetSelectionReview

noncomputable section
open Set Metric Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCOriginalSixteenBufferReview

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

private theorem interval_segments (x y : ball (0 : ℝ) (16 * (1 : ℝ))) :
    ∃ f : unitInterval → ball (0 : ℝ) (16 * (1 : ℝ)), Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ball (0 : ℝ) (16 * (1 : ℝ)) := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      exact (convex_ball (0 : ℝ) (16 * (1 : ℝ))) x.property y.property
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

private theorem interval_curves : ∀ a b : ball (0 : ℝ) (16 * (1 : ℝ)), ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ball (0 : ℝ) (16 * (1 : ℝ)), Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments interval_segments

local instance : LocallyCompactSpace (ball (0 : ℝ) (16 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

@[instance_reducible]
private noncomputable def actualMetric : MetricSpace (ball (0 : ℝ) (16 * (1 : ℝ))) :=
  intrinsicBallMetricSpace real_curves 0 (by norm_num)

private theorem actual_dist (a b : ball (0 : ℝ) (16 * (1 : ℝ))) :
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
    ∀ z : ball (0 : ℝ) (16 * (1 : ℝ)), ∃ Ω : Set (ball (0 : ℝ) (16 * (1 : ℝ))),
      @IsOpen _ actualMetric.toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ actualMetric κ Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
    (by norm_num) z).mpr (ambient_local z hκ)


theorem original_intrinsic_sixteen_comparison {κ : ℝ} (hκ : 0 ≤ κ) :
    @fourPointComparison (ball (0 : ℝ) (16 * (1 : ℝ))) actualMetric κ
      (@ball _ actualMetric.toPseudoMetricSpace ⟨0, by norm_num [Metric.mem_ball]⟩ 1) :=
  fourPointComparison_intrinsic_ball_of_16_buffer real_curves 0 hκ (by norm_num)
    (actual_local hκ)

theorem original_ambient_sixteen_comparison {κ : ℝ} (hκ : 0 ≤ κ) :
    fourPointComparison κ (ball (0 : ℝ) 1) :=
  fourPointComparison_ambient_ball_of_intrinsic_16_buffer real_curves 0 hκ (by norm_num)
    (actual_local hκ)

private def innerEndpoint : ball (0 : ℝ) (16 * (1 : ℝ)) :=
  ⟨99/100, by norm_num [Metric.mem_ball, Real.dist_eq]⟩

private def outerBufferPoint : ball (0 : ℝ) (16 * (1 : ℝ)) :=
  ⟨1599/100, by norm_num [Metric.mem_ball, Real.dist_eq]⟩

theorem original_endpoint_comparison_near_inner_boundary {κ : ℝ} (hκ : 0 ≤ κ) :
    @endpointHingeComparison _ actualMetric κ innerEndpoint (45 / 11) := by
  have hh := endpointHingeComparison_intrinsic_16_buffer real_curves 0 hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ)
    (p := innerEndpoint) (by norm_num [innerEndpoint, Metric.mem_ball, Real.dist_eq])
  simpa using hh

theorem original_complete_buffer_reaches_near_outer_boundary :
    @IsComplete _ actualMetric.toUniformSpace
      (@closedBall _ actualMetric.toPseudoMetricSpace innerEndpoint 15) ∧
    outerBufferPoint ∈ @closedBall _ actualMetric.toPseudoMetricSpace innerEndpoint 15 ∧
    @dist _ actualMetric.toDist outerBufferPoint innerEndpoint = 15 ∧
    15 < dist (outerBufferPoint : ℝ) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isComplete_intrinsicBall_closedBall real_curves 0 (by norm_num) innerEndpoint
      (r := 15) (by norm_num [innerEndpoint, Real.dist_eq])
  · change @dist _ actualMetric.toDist outerBufferPoint innerEndpoint ≤ 15
    rw [actual_dist]
    norm_num [innerEndpoint, outerBufferPoint, Real.dist_eq]
  · rw [actual_dist]
    norm_num [innerEndpoint, outerBufferPoint, Real.dist_eq]
  · norm_num [outerBufferPoint, Real.dist_eq]

theorem actual_intrinsic_open_ball_is_incomplete :
    ¬ @CompleteSpace _ actualMetric.toUniformSpace := by
  intro hc
  have hi : @Isometry (ball (0 : ℝ) (16 * (1 : ℝ))) ℝ
      actualMetric.toPseudoEMetricSpace inferInstance (fun a => (a : ℝ)) :=
    @Isometry.of_dist_eq _ _ actualMetric.toPseudoMetricSpace _ _
      (fun a b => (actual_dist a b).symm)
  have he := @Isometry.isClosedEmbedding (ball (0 : ℝ) (16 * (1 : ℝ))) ℝ
    actualMetric.toEMetricSpace hc inferInstance _ hi
  have hclosed : IsClosed (ball (0 : ℝ) (16 * (1 : ℝ))) := by
    simpa only [Subtype.range_val] using
      @Topology.IsClosedEmbedding.isClosed_range _ ℝ
        actualMetric.toUniformSpace.toTopologicalSpace inferInstance _ he
  have hmem : (16 : ℝ) ∈ closure (ball (0 : ℝ) (16 * (1 : ℝ))) := by
    rw [closure_ball 0 (by norm_num)]
    norm_num [Metric.mem_closedBall, Real.dist_eq]
  rw [hclosed.closure_eq] at hmem
  norm_num [Metric.mem_ball, Real.dist_eq] at hmem


theorem original_nonzero_curvature_near_boundary_configuration :
    comparisonAngleNegCurvature 2 (99/100) (99/100) (198/100) +
      comparisonAngleNegCurvature 2 (99/100) (98/100) (197/100) +
      comparisonAngleNegCurvature 2 (98/100) (99/100) (1/100) ≤ 2 * Real.pi := by
  have hh := original_ambient_sixteen_comparison (κ := 2) (by norm_num)
    (0 : ℝ) (by norm_num [Metric.mem_ball])
    (99/100) (by norm_num [Metric.mem_ball, Real.dist_eq])
    (-99/100) (by norm_num [Metric.mem_ball, Real.dist_eq])
    (98/100) (by norm_num [Metric.mem_ball, Real.dist_eq])
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.dist_eq] at hh ⊢
  exact hh

end GCOriginalSixteenBufferReview

#print axioms Metric.exists_relative_almost_minimum_with_budget
#print axioms Metric.MinimizingHinge.modelSide_ge_dist_of_complete_budget_buffer
#print axioms Metric.MinimizingHinge.comparisonAngle_le_of_complete_budget_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.endpointHingeComparison_of_complete_budget_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison_ball_of_complete_vertex_budget_buffers
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.endpointHingeComparison_intrinsic_16_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison_intrinsic_ball_of_16_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.fourPointComparison_ambient_ball_of_intrinsic_16_buffer
#print axioms GCBudgetSelectionReview.exists_moved_almost_minimum
#print axioms GCBudgetSelectionReview.zero_decay_parameter
#print axioms GCOriginalSixteenBufferReview.original_intrinsic_sixteen_comparison
#print axioms GCOriginalSixteenBufferReview.original_ambient_sixteen_comparison
#print axioms GCOriginalSixteenBufferReview.original_endpoint_comparison_near_inner_boundary
#print axioms GCOriginalSixteenBufferReview.original_complete_buffer_reaches_near_outer_boundary
#print axioms GCOriginalSixteenBufferReview.actual_intrinsic_open_ball_is_incomplete
#print axioms GCOriginalSixteenBufferReview.original_nonzero_curvature_near_boundary_configuration
#lint- only unusedArguments simpNF synTaut
```
