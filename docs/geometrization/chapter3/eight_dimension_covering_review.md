# Original eight-radius dimension covering acceptance

Four public theorems and four compiler-generated declarations in two leaves add eight owned declarations. The 400-module gate checks 1810 declarations in 3235 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import selected lint is silent; nine reports cover all four production theorems and five original-input regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root, PDF or Overleaf build, or human approval is claimed.

Root read both final production bodies, the entire frozen regression body, the actual comparison/chart/dimension/scaling dependencies, and the frozen blueprint contract passages. The result derives local compactness and the actual nearby chart from the original open eight-radius geometry and ambient Hausdorff dimension. Its internal net has strict epsilon coverage and the exact natural-ceiling count, on the same original closed ball. Both ambient and intrinsic comparison inputs are supported. Curvature zero is handled separately; positive bounded curvature uses the actual rescaled metric and returns the same finite set of original points. The singleton branch and every curvature in the stated range are covered by the tests.

The existing full same-limit extraction is unchanged. The alternate tangent/direction construction remains separate work. Blueprint207 and migration interfaces are unchanged.

# Independent original-eight-radius covering review

Verdict: mathematical proof and scope review passes. No independent compiler claim is made in this read-only review; the implementer has supplied separate final compile, lint, axiom, and original-input test evidence.

Frozen bodies:
- `gc_EightFiniteDimensionalCovering_body.lean`: SHA256 a7b5e0737fab628dbedd0235032be03d950f7485a712a43258ed6da5c39a7cef
- `gc_EightVaryingCurvatureCovering_body.lean`: SHA256 091a96a9441513ace78a4859ac7bdc90d8597c6a851e4431b008000b9e62f797

Read all four public declarations and proofs, and the accepted load-bearing NearbyPairedChart, ChartNetBound, RescaleNetBound, and EightChartCovering leaves. These compose the original AC04 eight-radius contraction/chart covering contract, now using the independent paired-configuration nearby chart and dimension-to-local-compactness producers. The current source/contract record is `/tmp/gc_EightDimensionCovering_record.md`; this review introduces no new source theorem or revised mathematical contract.

The fixed-curvature proof derives local compactness on exactly the open 8R ball, retains its actual nearby chart, uses the original eight-radius covering producer, and raises the exponent/dimension m to n with the same distortion `pairedChartDistortion n`. The separate singleton branch is valid and retains a net in the original closed ball. Intrinsic local comparison is transferred by the accepted exact local equivalence; no completeness or local compactness of the intrinsic open ball is silently added.

The varying-curvature proof first handles kappa=0, then uses the actual sqrt(kappa) metric rescaling for kappa>0. The controlled ball, Hausdorff dimension, completeness, and short-curve premise are transported exactly. The resulting Finset remains a set of the original source points, its closed-ball inclusion and strict epsilon-net property are transported back, and the numerical bound follows from the accepted sinh convexity inequality with sqrt(kappa)<=1. No curvature monotonicity for positive kappa is assumed. No source properness or larger-radius hypothesis is introduced.

No findings. Review performed by `/root/ac65_same_lines`; no repository edits or shared builds.

```lean
import DifferentialGeometry.Geometry.Comparison.EightFiniteDimensionalCovering
import DifferentialGeometry.Geometry.Comparison.EightVaryingCurvatureCovering
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



private theorem dim_eight : dimH (ball (0 : ℝ) (8 * (1 : ℝ))) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using
    (dimH_mono (subset_univ (ball (0 : ℝ) (8 * (1 : ℝ))))).trans_eq Real.dimH_univ

private def RealNet (ε : ℝ) : Prop :=
  ∃ T : Finset ℝ,
    T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1)^2 * Real.sinh (2 : ℝ) / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall (0 : ℝ) (1 : ℝ) ∧
      ∀ x ∈ closedBall (0 : ℝ) (1 : ℝ), ∃ y ∈ T, dist x y < ε

theorem original_ambient_eight_cover {ε : ℝ} (hε : 0 < ε) : RealNet ε := by
  have h := exists_closedBall_net_of_local_eight_comparison_and_dimH real_curves (0 : ℝ)
    (by norm_num : 0 < (1 : ℝ)) hε (n := 1) (by norm_num) dim_eight
    (fun z _ => ambient_local z (by norm_num))
  simpa only [RealNet, Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

theorem original_intrinsic_eight_cover {ε : ℝ} (hε : 0 < ε) : RealNet ε := by
  have h := exists_closedBall_net_of_intrinsic_local_eight_comparison_and_dimH real_curves (0 : ℝ)
    (by norm_num : 0 < (1 : ℝ)) hε (n := 1) (by norm_num) dim_eight (actual_local (by norm_num))
  simpa only [RealNet, Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

theorem original_bounded_ambient_eight_cover {κ ε : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) : RealNet ε := by
  have h := exists_closedBall_net_of_bounded_eight_local_curvature_and_dimH real_curves (0 : ℝ)
    hκ hκ1 (by norm_num : 0 < (1 : ℝ)) hε (n := 1) (by norm_num) dim_eight
    (fun z _ => ambient_local z hκ)
  simpa only [RealNet, Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

theorem original_bounded_intrinsic_eight_cover {κ ε : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) : RealNet ε := by
  have h := exists_closedBall_net_of_bounded_intrinsic_eight_local_curvature_and_dimH real_curves (0 : ℝ)
    hκ hκ1 (by norm_num : 0 < (1 : ℝ)) hε (n := 1) (by norm_num) dim_eight (actual_local hκ)
  simpa only [RealNet, Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

private abbrev Point := PUnit.{1}

private theorem point_segments (x y : Point) :
    ∃ f : unitInterval → Point, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  have hy : y = x := Subsingleton.elim _ _
  subst y
  exact ⟨fun _ => x, continuous_const, rfl, rfl, by simp⟩

theorem original_singleton_bounded_eight_cover {κ ε : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ T : Finset Point,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1)^2 * Real.sinh (4 : ℝ) / ε⌉₊ ∧
        (T : Set Point) ⊆ closedBall (PUnit.unit : Point) (2 : ℝ) ∧
        ∀ x ∈ closedBall (PUnit.unit : Point) (2 : ℝ), ∃ y ∈ T, dist x y < ε := by
  have hd : dimH (ball (PUnit.unit : Point) (8 * (2 : ℝ))) ≤ (1 : ℕ) := by
    rw [dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)]
    positivity
  have hlocal : ∀ z ∈ ball (PUnit.unit : Point) (8 * (2 : ℝ)),
      ∃ Ω : Set Point, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
    intro z _
    refine ⟨univ, isOpen_univ, ?_, mem_univ z⟩
    intro x _ a _ b _ c _ ha hb hc
    exact (ha (Subsingleton.elim _ _)).elim
  have h := exists_closedBall_net_of_bounded_eight_local_curvature_and_dimH
    (arbitrarily_short_curves_of_metric_segments point_segments) (PUnit.unit : Point)
    hκ hκ1 (by norm_num : 0 < (2 : ℝ)) hε (n := 1) (by norm_num) hd hlocal
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one, show (2 : ℝ)*2=4 by norm_num] using h

end GCOriginalEightMidpointReview

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_closedBall_net_of_local_eight_comparison_and_dimH
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_closedBall_net_of_intrinsic_local_eight_comparison_and_dimH
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_closedBall_net_of_bounded_eight_local_curvature_and_dimH
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_closedBall_net_of_bounded_intrinsic_eight_local_curvature_and_dimH
#print axioms GCOriginalEightMidpointReview.original_ambient_eight_cover
#print axioms GCOriginalEightMidpointReview.original_intrinsic_eight_cover
#print axioms GCOriginalEightMidpointReview.original_bounded_ambient_eight_cover
#print axioms GCOriginalEightMidpointReview.original_bounded_intrinsic_eight_cover
#print axioms GCOriginalEightMidpointReview.original_singleton_bounded_eight_cover
#lint- only unusedArguments simpNF synTaut
```
