# Exact one-dimensional recognition: compiled self-review

This is assistant self-review, not independent human/agent approval.
The curvature/dimension producer is now complete for the stated global
comparison scope: a rank-two packet contradicts the actual Hausdorff ceiling;
a segment's original endpoints create the rank-one packet; AC27 derives
local distance-coordinate injectivity. Exact equality with the original
segment then supplies open interiors. The earlier no-exit and endpoint
proofs consume this result, not an assumed local-recognition premise.
All charts are pointed isometries for the restricted ambient metric on the
actual ball, retaining endpoints and allowing the radius to depend on p.
The singleton branch returns an actual isometry, not just a proposition about
cardinality. Properness is not used: compactness of each segment suffices.
The full theorem remains under global zero-curvature four-point comparison.

The actual product and pointed-limit consumers inherit factor completeness,
segments and comparison, use the proved covering-based dimension drop, and
apply recognition to that same factor. They do not select a replacement
limit or split a different carrier. No global model classification, line
production, curvature-to-covering production or PC release binding is inferred.

All six new leaves and source-copy unusedArguments, simpNF and synTaut
linters compile silently. defLemma is unavailable; declaration kinds were
inspected manually. The 105-module gate passes (2893 jobs, 677 owned constants),
with only standard propext/Classical.choice/Quot.sound in new axiom closures.
The inherited AreaUpperBarrier warning lies outside them. Earlier math leaves
are unchanged. Blueprint207 is unchanged and its static audit passes. No
migrated full-root, PDF or Overleaf build is claimed.

The compiled driver proves real-line zero-curvature comparison and explicit
metric segments, then checks the full pointed recognition theorem, the exact
ball equality for an original interval, and short curves for coincident
endpoints. It exercises the full singleton alternative on PUnit and the full
pointed-chart disjunction at the endpoint of the closed ray, proving the ray's
segments, inherited comparison and Hausdorff bound. It does not separately
select the half-interval branch in that last example; the existing endpoint
consumer tests and its now-supplied openness proof cover that argument.
The driver and axiom queries compile without warnings.

```lean
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
import DifferentialGeometry.Geometry.Metric.Approximation.FactorRecognition
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature 0 (dist x a) (dist x b) (dist a b) = 0 := by
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
  exact comparisonAngleNegCurvature_abs_sub (by norm_num) (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison : fourPointComparison 0 (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc 0 (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 0 (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 0 (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) : ∃ f : Icc (0 : ℝ) 1 → ℝ,
    Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
    ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : Icc (0 : ℝ) 1 → ℝ := fun t => x + (y-x) * t
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(x + (y-x)*(s : ℝ)) - (x + (y-x)*(t : ℝ))| = |x-y| * |(s : ℝ)-t|
  have heq : (x + (y-x)*(s : ℝ)) - (x + (y-x)*(t : ℝ)) = (y-x)*((s : ℝ)-t) := by ring
  rw [heq, abs_mul, abs_sub_comm y x]

example (p : ℝ) : ∃ r : ℝ, ∃ hr : 0 < r,
    (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : ℝ) = p) ∨
    (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : ℝ) = p) := by
  exact exists_pointed_interval_or_half_interval_of_dimH_le_one real_segments real_comparison
    (fun z => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩) (by rw [Real.dimH_univ]) p

example : ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = 2 ∧ c 1 = 2 ∧
    eVariationOn c univ < ENNReal.ofReal (dist (2 : ℝ) 2 + 1) :=
  arbitrarily_short_curves_of_metric_segments real_segments 2 2 1 (by norm_num)

example : ball (0 : ℝ) (1/2) =
    ((↑) : Icc (-1 : ℝ) 1 → ℝ) '' {t | dist t (⟨0, by norm_num⟩ : Icc (-1 : ℝ) 1) < 1/2} := by
  have h := ball_eq_segment_image_of_dimH_le_one real_segments real_comparison
    (fun z => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩) (by rw [Real.dimH_univ])
    (σ := ((↑) : Icc (-1 : ℝ) 1 → ℝ)) isometry_subtype_coe
    (⟨0, by norm_num⟩ : Icc (-1 : ℝ) 1) (r := 1/2) (by norm_num)
  exact h

example : Nonempty (PUnit.{1} ≃ᵢ PUnit.{1}) ∨ ∀ p : PUnit.{1}, ∃ r : ℝ, ∃ hr : 0 < r,
    (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : PUnit.{1}) = p) ∨
    (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : PUnit.{1}) = p) := by
  apply singleton_or_pointed_interval_charts_of_dimH_le_one
  · intro x y
    refine ⟨fun _ => PUnit.unit, continuous_const, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
    intro s t
    simp
  · intro x hx a ha b hb c hc hax
    exact False.elim (hax (Subsingleton.elim _ _))
  · rw [dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)]
    norm_num

private theorem ray_segments (x y : Ici (0 : ℝ)) : ∃ f : Icc (0 : ℝ) 1 → Ici (0 : ℝ),
    Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
    ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : Icc (0 : ℝ) 1 → Ici (0 : ℝ) := fun t =>
    ⟨(1-(t : ℝ)) * x + (t : ℝ) * y,
      add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property)
        (mul_nonneg t.property.1 y.property)⟩
  refine ⟨f, by fun_prop, ?_, ?_, ?_⟩
  · apply Subtype.ext; simp [f]
  · apply Subtype.ext; simp [f]
  · intro s t
    change |((1-(s : ℝ)) * x + (s : ℝ) * y) - ((1-(t : ℝ)) * x + (t : ℝ) * y)| =
      |(x : ℝ)-y| * |(s : ℝ)-t|
    have heq : ((1-(s : ℝ)) * x + (s : ℝ) * y) - ((1-(t : ℝ)) * x + (t : ℝ) * y) =
        ((y : ℝ)-x)*((s : ℝ)-t) := by ring
    rw [heq, abs_mul, abs_sub_comm (y : ℝ) x]

example : ∃ r : ℝ, ∃ hr : 0 < r,
    (∃ e : Ioo (-r) r ≃ᵢ ball (⟨0, by norm_num⟩ : Ici (0 : ℝ)) r,
      (e ⟨0, by constructor <;> linarith⟩ : Ici (0 : ℝ)) = ⟨0, by norm_num⟩) ∨
    (∃ e : Ico (0 : ℝ) r ≃ᵢ ball (⟨0, by norm_num⟩ : Ici (0 : ℝ)) r,
      (e ⟨0, le_rfl, hr⟩ : Ici (0 : ℝ)) = ⟨0, by norm_num⟩) := by
  let : CompleteSpace (Ici (0 : ℝ)) := isClosed_Ici.completeSpace_coe
  let : Nontrivial (Ici (0 : ℝ)) := ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
    intro h
    have hh := congrArg (fun z : Ici (0 : ℝ) => (z : ℝ)) h
    norm_num at hh⟩⟩
  have hdim : dimH (univ : Set (Ici (0 : ℝ))) ≤ 1 := by
    rw [← isometry_subtype_coe.dimH_image]
    exact (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ
  exact exists_pointed_interval_or_half_interval_of_dimH_le_one ray_segments
    (real_comparison.of_isometry isometry_subtype_coe)
    (fun z => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩) hdim ⟨0, by norm_num⟩

#print axioms singleton_or_pointed_interval_charts_of_dimH_le_one
#print axioms exists_injOn_dist_ball_at_segment_interior_of_dimH_le_one
#print axioms GC.MetricGeometry.PointedGHConverges.singleton_or_pointed_interval_charts_factor
```
