# Compiled self-review: actual positive metric normalization

Nine public theorems and one definition in four leaves add twenty owned
declarations. The217-module gate passes for1120 owned declarations (3051
jobs); all transitive axiom closures use only propext, Classical.choice and
Quot.sound. Source-copy unusedArguments, simpNF and synTaut linters are
silent. Declaration kinds were inspected manually; defLemma is unavailable.
The inherited AreaUpperBarrier admission warning remains outside these
closures. Earlier mathematical leaves are unchanged. Static audit passes;
no full migrated root, PDF, Overleaf, human or delegated review is claimed.

The compiled review uses the actual real-line metric scaled by1/2. It checks
that the distance from-3 to7 becomes5, completeness, dimension1, and exact
open/closed ball identities for arbitrary real radii (thus also zero and
negative radii). Actual arbitrarily short curves between those distinct
points have rescaled variation below5+epsilon for every positive epsilon.
Comparison at kappa1/4 is normalized in the actual sqrt(kappa)-scaled metric;
both global and local comparison consumers are exercised. The literal
rank3 ceiling bound is compared at scale1/2 with arbitrary positive mesh.
The review metric is explicitly instance-reducible, and the final driver
compiles with exit zero and only the ten axiom reports.

The statement audit checks that c>0 is retained in all metric constructions,
that kappa>0 is required for sqrt normalization, and that the numerical
comparison additionally requires c<=1. Metric/topological parents are
explicit wherever two structures share a type. Variation is proved from
actual partition sums, without assuming finite variation or continuity;
continuity is used only in the subsequent length-space transport. The
radius and error are both scaled, and the final coefficient is independent
of c. There is no general curvature-monotonicity claim and no conversion of
metric scaling into an unproved Riemannian tensor statement. The separate
zero-curvature route, growing-region assembly and sharp8R qualifications
are preserved.

```lean
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleLength
import DifferentialGeometry.Geometry.Comparison.RescaleComparison
import DifferentialGeometry.Topology.MetricSpace.RescaleNetBound
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

@[instance_reducible]
private noncomputable def halfMetric : MetricSpace ℝ :=
  (inferInstance : MetricSpace ℝ).rescale (1 / 2) (by norm_num)

example : @dist ℝ halfMetric.toDist (-3) 7 = 5 := by
  change (1 / 2 : ℝ) * dist (-3 : ℝ) 7 = 5
  norm_num [Real.dist_eq]

example : @CompleteSpace ℝ halfMetric.toUniformSpace :=
  (MetricSpace.rescale_completeSpace_iff (inferInstance : MetricSpace ℝ)
    (1 / 2) (by norm_num)).mpr inferInstance

example : @dimH ℝ halfMetric.toEMetricSpace univ = 1 := by
  rw [show halfMetric = (inferInstance : MetricSpace ℝ).rescale (1 / 2) (by norm_num) from rfl,
    MetricSpace.rescale_dimH, Real.dimH_univ]

example (r : ℝ) : @ball ℝ halfMetric.toPseudoMetricSpace 3 ((1 / 2) * r) = ball 3 r :=
  MetricSpace.rescale_ball (inferInstance : MetricSpace ℝ) (1 / 2) (by norm_num) 3 r

example (r : ℝ) : @closedBall ℝ halfMetric.toPseudoMetricSpace 3 ((1 / 2) * r) = closedBall 3 r :=
  MetricSpace.rescale_closedBall (inferInstance : MetricSpace ℝ) (1 / 2) (by norm_num) 3 r

example (η : ℝ) (hη : 0 < η) :
    ∃ f : unitInterval → ℝ,
      @Continuous unitInterval ℝ inferInstance halfMetric.toUniformSpace.toTopologicalSpace f ∧
      f 0 = -3 ∧ f 1 = 7 ∧
      @eVariationOn unitInterval inferInstance ℝ halfMetric.toUniformSpace.toTopologicalSpace
        (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℝ halfMetric.toPseudoEMetricSpace) f univ <
          ENNReal.ofReal (5 + η) := by
  have h := MetricSpace.rescale_arbitrarily_short_curves real_curves
    (1 / 2) (by norm_num) (-3) 7 hη
  have hd : @dist ℝ halfMetric.toDist (-3) 7 = 5 := by
    change (1 / 2 : ℝ) * dist (-3 : ℝ) 7 = 5
    norm_num [Real.dist_eq]
  change ∃ f : unitInterval → ℝ,
    @Continuous unitInterval ℝ inferInstance halfMetric.toUniformSpace.toTopologicalSpace f ∧
      f 0 = -3 ∧ f 1 = 7 ∧
      @eVariationOn unitInterval inferInstance ℝ halfMetric.toUniformSpace.toTopologicalSpace
        (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℝ halfMetric.toPseudoEMetricSpace) f univ <
          ENNReal.ofReal (@dist ℝ halfMetric.toDist (-3) 7 + η) at h
  rwa [hd] at h

example : @fourPointComparison ℝ
    ((inferInstance : MetricSpace ℝ).rescale (Real.sqrt (1 / 4))
      (Real.sqrt_pos.mpr (by norm_num))) 1 univ :=
  (fourPointComparison_rescale_sqrt_iff (by norm_num : (0 : ℝ) < 1 / 4) univ).mpr
    (real_comparison (by norm_num))

example (p : ℝ) : ∃ Ω : Set ℝ,
    @IsOpen ℝ ((inferInstance : MetricSpace ℝ).rescale (Real.sqrt (1 / 4))
      (Real.sqrt_pos.mpr (by norm_num))).toUniformSpace.toTopologicalSpace Ω ∧
    @fourPointComparison ℝ ((inferInstance : MetricSpace ℝ).rescale (Real.sqrt (1 / 4))
      (Real.sqrt_pos.mpr (by norm_num))) 1 Ω ∧ p ∈ Ω :=
  (local_fourPointComparison_rescale_sqrt_iff (by norm_num : (0 : ℝ) < 1 / 4) p).mpr
    (ambient_local p (by norm_num))

example (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (1 + ⌈4 * L ^ 2 * Real.sqrt 3 * Real.sinh (2 * ((1 / 2) * 2)) / ((1 / 2) * ε)⌉₊) ^ 3 ≤
      (1 + ⌈4 * L ^ 2 * Real.sqrt 3 * Real.sinh (2 * 2) / ε⌉₊) ^ 3 := by
  simpa only [Nat.cast_ofNat] using chart_net_bound_rescale_le
    (n := 3) (L := L) (R := 2) (c := 1 / 2) (by norm_num) hε (by norm_num) (by norm_num)

#print axioms MetricSpace.rescaleUniformEquiv
#print axioms MetricSpace.rescale_completeSpace_iff
#print axioms MetricSpace.rescale_dimH
#print axioms MetricSpace.rescale_ball
#print axioms MetricSpace.rescale_closedBall
#print axioms MetricSpace.rescale_eVariationOn_le
#print axioms MetricSpace.rescale_arbitrarily_short_curves
#print axioms fourPointComparison_rescale_sqrt_iff
#print axioms local_fourPointComparison_rescale_sqrt_iff
#print axioms chart_net_bound_rescale_le
```
