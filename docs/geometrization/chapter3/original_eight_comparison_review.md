# Full original AC64 and original-endpoint AC02 acceptance

Seven public theorems and one private helper in six leaves add eight owned declarations. The381-module gate checks1762 declarations in3216 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import selected lint is silent;19 reports cover all seven production theorems and twelve concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root read all six final production bodies and the entire frozen regression body; independent peer review checked the original contracts, actual midpoint/interpolation proof and its intrinsic metric use. Full original AC64 is proved at8r<L for both SAME original radial isometries on possibly different domains, with independent shortening parameters. The AC02 result in this milestone is the original-endpoint point-on-side component only. Full arbitrary radial subtriangles are explicitly separate work.

# Independent review: original AC64 and first-side AC02

Reviewer: half_angle sub-agent. Temporary files only; no repository edits or builds.

## Source and contract

Read frozen blueprint `master207A.tex` AC64 lines 5374–5421 and AC02 lines 2141–2190, and the source/proof record `/tmp/gc_OriginalEightComparison_record.md`. Earlier checks retained here: AKP `defs-CBB.tex` at commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, key-lem:globalization, lines 953–1090; archived KL local-collapse Section 3.3 printed 22–23/PDF17–18 and recorded corrections. The new proof route is explicitly the actual long–short midpoint/cosh maximum-principle route; it is not an assertion that a citation supplies the source's precise complete-buffer theorem.

The full AC64 wrapper retains complete ambient X, actual arbitrarily short curves, local comparison only on the original OPEN ball of radius L, dimension bound on that ball, kappa>0 and 0<8r<L. Local compactness is produced from the given data. Both original supplied radial segments may have distinct lengths A,B>=r. The output evaluates these very functions at the original r,s,t and uses ambient distances. No extension, replacement geodesic, comparison at radius L, or curvature-zero claim is hidden.

The first-side AC02 theorem retains q in OPEN ball R/2, x,z in CLOSED ball R, the actual supplied segment q→x, and every parameter including zero and the endpoint. It proves vertex-to-side model distance comparison. It does not assert the full arbitrary-subtriangle clause; a prefix used as a new opposite vertex need not remain in closed ball R.

## Proof review

All reviewed proof bodies pass mathematical and Lean-contract review. The intrinsic midpoint proof uses the actual intrinsic metric explicitly, with a complete radius27R/4 buffer centered at z even when z lies on the closed radiusR boundary. The available comparison threshold45R/22 exceeds2R. The original open intrinsic ball need not be complete. Original supplied sigma and its real parameters survive the lift and descent unchanged.

The interpolation proof invokes midpoint comparison only at a hypothetical point where cosh(distance) lies below the interpolant. The interpolant is bounded above by the maximum endpoint cosh, so at that point the actual distance is strictly below2R. No global bound on all segment-to-z distances is incorrectly assumed. Continuity and endpoint inequalities include equality at2R.

The one-side angle theorem applies the scalar cosh interpolation bridge with a positive long arm. The two-radial theorem first shortens the original gamma, then the original beta; sign/order swaps are exactly comparison-angle symmetry and distance symmetry. The original-input wrapper restricts the supplied segments via value-preserving subtype inclusions, so no new segment family is selected.

The first-side theorem handles t=0 and q=z separately, bounds the same supplied segment inside closed ball3R/2 by its two endpoint triangle inequalities, and converts the actual angle inequality to model-side inequality using the exact metric-triangle identity. The zero whole segment is included by the t=0 branch.

## Frozen candidates and evidence

- IntrinsicEightInterpolation body SHA256 1d8300bc32938456f5c33c7b3737cd5215dd21b4122ebc6fb27a82933f36c193.
- IntrinsicEightRadialComparison body SHA256 54b734aa109caadcbfbf026c5158ac1c2e987dd45cf3a4264b0ac79656bd4f55.
- OriginalEightRadialComparison body SHA256 38af9dfca066f011e1bcd8aaee3c902458fdfb59f596a517a9976e21e0654234.
- OriginalEightPointOnSide body SHA256 9da9670e5aacf04b7014747fc582f233fffc086e77eddb70b46c75bc386ea5ee.
- Self-contained regression body `/tmp/gc_original_eight_comparison_review_body.lean`, SHA256 ea984237eafc27ea36033b49a943bd64493c356e40969e01621af1784c5558e2.
- Combined driver `/tmp/gc_original_eight_comparison_review_agent.lean`, SHA256 8388975cf9593194d9a2c0c2b3818c6667adadb90e5130406f3def1e723ba4b9.
- Lint driver/log `/tmp/gc_original_eight_comparison_review_lint.lean` / `.log`: compiler exit0, all12 regression declarations plus first-side production declaration use exactly propext, Classical.choice, Quot.sound; unusedArguments/simpNF/synTaut silent.
- Earlier four-declaration independent production closure and six-new-test lint: `/tmp/gc_original_eight_radial_review_lint.log`, exit0, standard three only.

The regression body contains one fixture, not concatenated duplicate declarations. Imports needed with canonical production modules: DifferentialGeometry.Topology.MetricSpace.SegmentCurves; Mathlib.Analysis.Normed.Module.Convex; Mathlib.Tactic.

Twelve public tests: original intrinsic8 midpoint at z=-1,t=149/100; zero long-arm midpoint; complete27/4 buffer with actual exact boundary point and explicit failed7R outer boundary; original AC64 at kappa4,L9,r1,A2,B3,s1/3,t2/3; actual angle-pi evaluation; endpoint times; coincident radial comparison; actual zero-angle evaluation; interpolation at exact endpoint-distance2R; first-side offcenter q=-1/4,x1,z=-1 for all parameters; first-side zero long arm; first-side zero whole segment. All source curves, local comparison, intrinsic distance equality and finite dimension used in applications are proved from the actual real-space data.

```lean
import DifferentialGeometry.Geometry.Comparison.LongShortMidpoint
import DifferentialGeometry.Geometry.Comparison.IntrinsicEightMidpoint
import DifferentialGeometry.Geometry.Comparison.IntrinsicEightInterpolation
import DifferentialGeometry.Geometry.Comparison.IntrinsicEightRadialComparison
import DifferentialGeometry.Geometry.Comparison.EightRadialComparison
import DifferentialGeometry.Geometry.Comparison.EightPointOnSide
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Metric Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCOriginalEightMidpointReview

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

private theorem interval_segments (x y : ball (0 : ℝ) (8 * (1 : ℝ))) :
    ∃ f : unitInterval → ball (0 : ℝ) (8 * (1 : ℝ)), Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ball (0 : ℝ) (8 * (1 : ℝ)) := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      exact (convex_ball (0 : ℝ) (8 * (1 : ℝ))) x.property y.property
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

private theorem interval_curves : ∀ a b : ball (0 : ℝ) (8 * (1 : ℝ)), ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ball (0 : ℝ) (8 * (1 : ℝ)), Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments interval_segments

local instance : LocallyCompactSpace (ball (0 : ℝ) (8 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

@[instance_reducible]
private noncomputable def actualMetric : MetricSpace (ball (0 : ℝ) (8 * (1 : ℝ))) :=
  intrinsicBallMetricSpace real_curves 0 (by norm_num)

private theorem actual_dist (a b : ball (0 : ℝ) (8 * (1 : ℝ))) :
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
    ∀ z : ball (0 : ℝ) (8 * (1 : ℝ)), ∃ Ω : Set (ball (0 : ℝ) (8 * (1 : ℝ))),
      @IsOpen _ actualMetric.toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison _ actualMetric κ Ω ∧ z ∈ Ω := by
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
    (by norm_num) z).mpr (ambient_local z hκ)


private def originalSegment (s : Icc (0 : ℝ) (3/2)) : ℝ := (s : ℝ) - 1/2

private theorem originalSegment_isometry : Isometry originalSegment := by
  apply Isometry.of_dist_eq
  intro s t
  change |((s : ℝ) - 1/2) - ((t : ℝ) - 1/2)| = |(s : ℝ) - t|
  congr 1
  ring

private theorem originalSegment_mem (s : Icc (0 : ℝ) (3/2)) :
    originalSegment s ∈ closedBall (0 : ℝ) (3 * 1 / 2) := by
  change |(s : ℝ) - 1/2 - 0| ≤ 3 * 1 / 2
  apply abs_le.mpr
  constructor <;> linarith [s.property.1, s.property.2]

theorem original_eight_buffer_midpoint_at_closed_boundary {κ : ℝ} (hκ : 0 < κ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 149/100 ∧ 149/100 + h ≤ 3/2 ∧
      Real.cosh (Real.sqrt κ * dist (-1 : ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (149/100 - h))) +
      Real.cosh (Real.sqrt κ * dist (-1 : ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (149/100 + h))) ≤
      2 * Real.cosh (Real.sqrt κ * h) *
        Real.cosh (Real.sqrt κ * dist (-1 : ℝ)
          (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (149/100))) := by
  apply exists_cosh_midpoint_of_intrinsic_8_buffer real_curves (0 : ℝ) hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num) originalSegment originalSegment_isometry originalSegment_mem
    (z := -1) (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    (t := 149/100) (by norm_num)
  norm_num [originalSegment, Real.dist_eq]

theorem original_eight_buffer_midpoint_at_segment_center {κ : ℝ} (hκ : 0 < κ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/2 ∧ 1/2 + h ≤ 3/2 ∧
      Real.cosh (Real.sqrt κ * dist (0 : ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (1/2 - h))) +
      Real.cosh (Real.sqrt κ * dist (0 : ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (1/2 + h))) ≤
      2 * Real.cosh (Real.sqrt κ * h) *
        Real.cosh (Real.sqrt κ * dist (0 : ℝ)
          (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment (1/2))) := by
  apply exists_cosh_midpoint_of_intrinsic_8_buffer real_curves (0 : ℝ) hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num) originalSegment originalSegment_isometry originalSegment_mem
    (z := 0) (by norm_num [Metric.mem_closedBall])
    (t := 1/2) (by norm_num)
  norm_num [originalSegment, Real.dist_eq]

private def boundaryEndpoint : ball (0 : ℝ) (8 * (1 : ℝ)) :=
  ⟨-1, by norm_num [Metric.mem_ball, Real.dist_eq]⟩

private def farBufferPoint : ball (0 : ℝ) (8 * (1 : ℝ)) :=
  ⟨-31/4, by norm_num [Metric.mem_ball, Real.dist_eq]⟩

theorem complete_buffer_at_closed_boundary_is_genuinely_interior :
    dist (boundaryEndpoint : ℝ) 0 = 1 ∧
    @IsComplete _ actualMetric.toUniformSpace
      (@closedBall _ actualMetric.toPseudoMetricSpace boundaryEndpoint (27/4)) ∧
    farBufferPoint ∈ @closedBall _ actualMetric.toPseudoMetricSpace boundaryEndpoint (27/4) ∧
    @dist _ actualMetric.toDist farBufferPoint boundaryEndpoint = 27/4 ∧
    dist (-8 : ℝ) (-1) = 7 ∧ (-8 : ℝ) ∉ ball 0 (8 * (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [boundaryEndpoint, Real.dist_eq]
  · exact isComplete_intrinsicBall_closedBall real_curves 0 (by norm_num) boundaryEndpoint
      (r := 27/4) (by norm_num [boundaryEndpoint, Real.dist_eq])
  · change @dist _ actualMetric.toDist farBufferPoint boundaryEndpoint ≤ 27/4
    rw [actual_dist]
    norm_num [boundaryEndpoint, farBufferPoint, Real.dist_eq]
  · rw [actual_dist]
    norm_num [boundaryEndpoint, farBufferPoint, Real.dist_eq]
  · norm_num [Real.dist_eq]
  · norm_num [Metric.mem_ball, Real.dist_eq]

end GCOriginalEightMidpointReview

noncomputable section
open Set Metric Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Analysis.ODE
namespace GCOriginalEightMidpointReview

private def suppliedPositive (u : Icc (0 : ℝ) 2) : ℝ := u
private def suppliedNegative (u : Icc (0 : ℝ) 3) : ℝ := -(u : ℝ)
private def suppliedCoincident (u : Icc (0 : ℝ) 3) : ℝ := u

private theorem suppliedPositive_isometry : Isometry suppliedPositive :=
  Isometry.of_dist_eq fun _ _ => rfl

private theorem suppliedNegative_isometry : Isometry suppliedNegative := by
  apply Isometry.of_dist_eq
  intro u v
  change |-(u : ℝ) - -(v : ℝ)| = |(u : ℝ) - v|
  rw [show -(u : ℝ) - -(v : ℝ) = -((u : ℝ) - v) by ring, abs_neg]

private theorem suppliedCoincident_isometry : Isometry suppliedCoincident :=
  Isometry.of_dist_eq fun _ _ => rfl

private theorem real_dim_nine : dimH (ball (0 : ℝ) 9) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using (dimH_mono (subset_univ (ball (0 : ℝ) 9))).trans_eq Real.dimH_univ

private theorem original_opposite_comparison {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedNegative ⟨1, by norm_num⟩)) ≤
    comparisonAngleNegCurvature 4 s t
      (dist (suppliedPositive ⟨s, ⟨hs.1.le, by linarith [hs.2]⟩⟩)
        (suppliedNegative ⟨t, ⟨ht.1.le, by linarith [ht.2]⟩⟩)) := by
  exact comparisonAngleNegCurvature_le_of_radial_isometries_in_eight_buffer
    real_curves 0 (by norm_num) (by norm_num) (by norm_num) real_dim_nine
    (fun z _ => ambient_local z (by norm_num)) (by norm_num) (by norm_num)
    suppliedPositive suppliedNegative suppliedPositive_isometry suppliedNegative_isometry
    rfl (by simp [suppliedNegative]) hs ht

theorem original_eight_buffer_unequal_supplied_segments :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedNegative ⟨1, by norm_num⟩)) ≤
    comparisonAngleNegCurvature 4 (1/3) (2/3)
      (dist (suppliedPositive ⟨1/3, by norm_num⟩) (suppliedNegative ⟨2/3, by norm_num⟩)) :=
  original_opposite_comparison (by norm_num) (by norm_num)

theorem original_eight_buffer_opposite_angles_are_pi :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedNegative ⟨1, by norm_num⟩)) = Real.pi ∧
    comparisonAngleNegCurvature 4 (1/3) (2/3)
      (dist (suppliedPositive ⟨1/3, by norm_num⟩) (suppliedNegative ⟨2/3, by norm_num⟩)) = Real.pi := by
  constructor
  · norm_num only [suppliedPositive, suppliedNegative, Real.dist_eq]
    convert comparisonAngleNegCurvature_add (by norm_num : (0 : ℝ) ≤ 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) using 1; norm_num
  · norm_num only [suppliedPositive, suppliedNegative, Real.dist_eq]
    convert comparisonAngleNegCurvature_add (by norm_num : (0 : ℝ) ≤ 4)
      (by norm_num : (0 : ℝ) < 1/3) (by norm_num : (0 : ℝ) < 2/3) using 1; norm_num

theorem original_eight_buffer_keeps_endpoint_times :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedNegative ⟨1, by norm_num⟩)) ≤
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedNegative ⟨1, by norm_num⟩)) :=
  original_opposite_comparison (by norm_num) (by norm_num)

theorem original_eight_buffer_coincident_radials :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedCoincident ⟨1, by norm_num⟩)) ≤
    comparisonAngleNegCurvature 4 (1/3) (2/3)
      (dist (suppliedPositive ⟨1/3, by norm_num⟩) (suppliedCoincident ⟨2/3, by norm_num⟩)) := by
  exact comparisonAngleNegCurvature_le_of_radial_isometries_in_eight_buffer
    real_curves 0 (by norm_num) (by norm_num) (by norm_num) real_dim_nine
    (fun z _ => ambient_local z (by norm_num)) (by norm_num) (by norm_num)
    suppliedPositive suppliedCoincident suppliedPositive_isometry suppliedCoincident_isometry
    rfl rfl (by norm_num) (by norm_num)

theorem original_eight_buffer_coincident_angles_are_zero :
    comparisonAngleNegCurvature 4 1 1
      (dist (suppliedPositive ⟨1, by norm_num⟩) (suppliedCoincident ⟨1, by norm_num⟩)) = 0 ∧
    comparisonAngleNegCurvature 4 (1/3) (2/3)
      (dist (suppliedPositive ⟨1/3, by norm_num⟩) (suppliedCoincident ⟨2/3, by norm_num⟩)) = 0 := by
  constructor
  · convert comparisonAngleNegCurvature_abs_sub (by norm_num : (0 : ℝ) ≤ 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) using 1;
      norm_num [suppliedPositive, suppliedCoincident, Real.dist_eq]
  · convert comparisonAngleNegCurvature_abs_sub (by norm_num : (0 : ℝ) ≤ 4)
      (by norm_num : (0 : ℝ) < 1/3) (by norm_num : (0 : ℝ) < 2/3) using 1;
      norm_num [suppliedPositive, suppliedCoincident, Real.dist_eq]

theorem original_eight_interpolation_includes_closed_distance_threshold {κ : ℝ} (hκ : 0 < κ) :
    ∀ t ∈ Icc (0 : ℝ) (3/2),
      hyperbolicInterpolate (Real.sqrt κ) (3/2)
        (Real.cosh (Real.sqrt κ * (1/2))) (Real.cosh (Real.sqrt κ * 2)) t ≤
      Real.cosh (Real.sqrt κ * dist (-1 : ℝ)
        (IccExtend (by norm_num : (0 : ℝ) ≤ 3/2) originalSegment t)) := by
  let : LocallyCompactSpace (ball (0 : ℝ) (8 * (1 : ℝ))) := isOpen_ball.locallyCompactSpace
  have hh := hyperbolicInterpolate_le_of_intrinsic_8_buffer real_curves 0 hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num) originalSegment originalSegment_isometry originalSegment_mem
    (z := -1) (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    (by norm_num [originalSegment, Real.dist_eq]) (by norm_num [originalSegment, Real.dist_eq])
  norm_num only [originalSegment, Real.dist_eq] at hh
  norm_num at hh
  intro t ht
  exact hh t ht.1 ht.2

end GCOriginalEightMidpointReview

noncomputable section
open Set Metric Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCOriginalEightMidpointReview

local instance : LocallyCompactSpace (ball (0 : ℝ) (8 * (1 : ℝ))) :=
  isOpen_ball.locallyCompactSpace

private def offcenterSegment (u : Icc (0 : ℝ) (dist (-1/4 : ℝ) 1)) : ℝ := (u : ℝ) - 1/4

private theorem offcenterSegment_isometry : Isometry offcenterSegment := by
  apply Isometry.of_dist_eq
  intro u v
  change |((u : ℝ) - 1/4) - ((v : ℝ) - 1/4)| = |(u : ℝ) - v|
  congr 1
  ring

theorem original_first_side_offcenter_and_closed_boundary {κ : ℝ} (hκ : 0 < κ)
    (t : Icc (0 : ℝ) (dist (-1/4 : ℝ) 1)) :
    modelSideNegCurvature κ t.val (dist (-1/4 : ℝ) (-1))
      (comparisonAngleNegCurvature κ (dist (-1/4 : ℝ) 1)
        (dist (-1/4 : ℝ) (-1)) (dist (1 : ℝ) (-1))) ≤ dist (offcenterSegment t) (-1) := by
  exact radial_point_on_side_of_intrinsic_8_buffer real_curves 0 hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num [Metric.mem_ball, Real.dist_eq])
    (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    offcenterSegment offcenterSegment_isometry
    (by norm_num [offcenterSegment]) (by norm_num [offcenterSegment, Real.dist_eq]) t

theorem original_first_side_zero_long_arm {κ : ℝ} (hκ : 0 < κ)
    (t : Icc (0 : ℝ) (dist (-1/4 : ℝ) 1)) :
    modelSideNegCurvature κ t.val (dist (-1/4 : ℝ) (-1/4))
      (comparisonAngleNegCurvature κ (dist (-1/4 : ℝ) 1)
        (dist (-1/4 : ℝ) (-1/4)) (dist (1 : ℝ) (-1/4))) ≤ dist (offcenterSegment t) (-1/4) := by
  exact radial_point_on_side_of_intrinsic_8_buffer real_curves 0 hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num [Metric.mem_ball, Real.dist_eq])
    (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    offcenterSegment offcenterSegment_isometry
    (by norm_num [offcenterSegment]) (by norm_num [offcenterSegment, Real.dist_eq]) t

private def zeroSegment (_ : Icc (0 : ℝ) (dist (0 : ℝ) 0)) : ℝ := 0

private theorem zeroSegment_isometry : Isometry zeroSegment := by
  apply Isometry.of_dist_eq
  intro u v
  have hu : (u : ℝ) = 0 := by have hh := u.property.2; simp only [dist_self] at hh; exact le_antisymm hh u.property.1
  have hv : (v : ℝ) = 0 := by have hh := v.property.2; simp only [dist_self] at hh; exact le_antisymm hh v.property.1
  simp [zeroSegment, Subtype.dist_eq, hu, hv]

theorem original_first_side_zero_segment {κ : ℝ} (hκ : 0 < κ)
    (t : Icc (0 : ℝ) (dist (0 : ℝ) 0)) :
    modelSideNegCurvature κ t.val (dist (0 : ℝ) 1)
      (comparisonAngleNegCurvature κ (dist (0 : ℝ) 0)
        (dist (0 : ℝ) 1) (dist (0 : ℝ) 1)) ≤ dist (zeroSegment t) 1 := by
  exact radial_point_on_side_of_intrinsic_8_buffer real_curves 0 hκ
    (by norm_num : (0 : ℝ) < 1) (actual_local hκ.le)
    (by norm_num [Metric.mem_ball]) (by norm_num [Metric.mem_closedBall])
    (by norm_num [Metric.mem_closedBall, Real.dist_eq])
    zeroSegment zeroSegment_isometry rfl rfl t

end GCOriginalEightMidpointReview

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.cosh_midpoint_le_of_endpoint_comparison
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_cosh_midpoint_of_intrinsic_8_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicInterpolate_le_of_intrinsic_8_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_intrinsic_8_buffer_segment
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_radial_isometries_intrinsic_8_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_radial_isometries_in_eight_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.radial_point_on_side_of_intrinsic_8_buffer
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_midpoint_at_closed_boundary
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_midpoint_at_segment_center
#print axioms GCOriginalEightMidpointReview.complete_buffer_at_closed_boundary_is_genuinely_interior
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_unequal_supplied_segments
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_opposite_angles_are_pi
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_keeps_endpoint_times
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_coincident_radials
#print axioms GCOriginalEightMidpointReview.original_eight_buffer_coincident_angles_are_zero
#print axioms GCOriginalEightMidpointReview.original_eight_interpolation_includes_closed_distance_threshold
#print axioms GCOriginalEightMidpointReview.original_first_side_offcenter_and_closed_boundary
#print axioms GCOriginalEightMidpointReview.original_first_side_zero_long_arm
#print axioms GCOriginalEightMidpointReview.original_first_side_zero_segment
#lint- only unusedArguments simpNF synTaut
```
