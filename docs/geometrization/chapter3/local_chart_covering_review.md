# Compiled self-review: AC04 exact uniform net bound

Three public theorems and nine generated declarations in two leaves add12
owned declarations. The208-module gate passes for1086 declarations (3042
build jobs). New transitive closures contain only propext, Classical.choice
and Quot.sound. Source-copy unusedArguments, simpNF and synTaut linters are
silent; defLemma is unavailable and kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no full migrated root, PDF,
Overleaf, human or delegated review is claimed.

The compiled integration example constructs an actual one-dimensional PiLp
chart on the real delta0-ball, proves its isometry by the finite L2 distance
formula, and uses ONLY original bounded local ambient comparison and actual
length curves to obtain an internal net of the closed unit ball. Delta0 and
epsilon are arbitrary positive reals. The final displayed bound is literally
1+ceil(4*sinh(2)/epsilon), with no delta0 term. This checks dimension1,
distortion1, arbitrary shrinking chart radii, strict coverage, internal
centers, and the exact natural-ceiling normalization. Initial driver-only
namespace/simplification issues were corrected; the final script compiled
with exit zero and only requested axiom reports.

Statement review follows the same constructed map from radial contraction
through the chart into the packing theorem, so there is no assumed packing
or net bound in the geometric consumer. The lower factor is positive, and
the original metric on the source subset is used. Exact cancellation of delta
precedes the ceiling step; monotonicity of powers has a proved nonnegative
base and the exponent is the actual chart dimension. The greedy theorem
returns centers in the original set and strict epsilon coverage. The local
comparison consumer explicitly retains the256R margin and does not infer
global source properness. The near-point chart itself remains a separate
producer; smooth-specialization bindings remain migration dependent.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalChartCovering
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

private noncomputable def line_chart {δ₀ : ℝ} (x : ball (0 : ℝ) δ₀) :
    PiLp 2 (fun _ : Fin 1 => ℝ) := WithLp.toLp 2 (fun _ => (x : ℝ))

private theorem line_chart_dist {δ₀ : ℝ} (u v : ball (0 : ℝ) δ₀) :
    dist (line_chart u) (line_chart v) = dist u v := by
  have hs : dist (line_chart u) (line_chart v) ^ 2 = dist u v ^ 2 := by
    rw [PiLp.dist_sq_eq_of_L2]
    simp [line_chart]
    rfl
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

example (δ₀ ε : ℝ) (hδ₀ : 0 < δ₀) (hε : 0 < ε) :
    ∃ T : Finset ℝ, T.card ≤ 1 + ⌈4 * Real.sinh 2 / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, ∃ y ∈ T, dist x y < ε := by
  have hzero : line_chart (⟨0, by simpa only [mem_ball, dist_self] using hδ₀⟩ : ball (0 : ℝ) δ₀) = 0 := by
    ext i
    simp [line_chart]
  have hlower : ∀ u v : ball (0 : ℝ) δ₀,
      (1 : ℝ)⁻¹ * dist u v ≤ dist (line_chart u) (line_chart v) := by
    intro u v
    rw [line_chart_dist, inv_one, one_mul]
  have hupper : ∀ u v : ball (0 : ℝ) δ₀,
      dist (line_chart u) (line_chart v) ≤ (1 : ℝ) * dist u v := by
    intro u v
    rw [line_chart_dist, one_mul]
  have ht := exists_closedBall_net_of_local_256_comparison_and_chart real_curves 0
    (by norm_num : (0 : ℝ) < 1) (fun z _ => ambient_local z (by norm_num))
    (q := 0) (by norm_num [mem_ball]) (n := 1) (by norm_num)
    (L := 1) (by norm_num) hδ₀ hε line_chart hzero hlower hupper
  simpa only [one_pow, pow_one, mul_one, Nat.cast_one, Real.sqrt_one] using ht

#print axioms exists_net_of_radial_contraction_and_chart
#print axioms exists_closedBall_net_of_comparison_and_chart
#print axioms exists_closedBall_net_of_local_256_comparison_and_chart
```
