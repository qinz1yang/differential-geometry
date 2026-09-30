# Compiled self-review: global endpoint recognition

Eight public theorems in five leaves pass the 144-module/810-owned-declaration
gate. Source-copy unusedArguments, simpNF and synTaut linters are silent.
defLemma is unavailable; declaration kinds were inspected manually. New
closures use only propext, Classical.choice and Quot.sound. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures; no full migrated-root or PDF build is claimed.
The blueprint static audit passes.

The driver proves actual ray segments, inherited zero-curvature comparison,
Hausdorff dimension at most one and the ray's metric endpoint condition,
then invokes the geometric global model theorem. It separately applies the
complete-image classifier to the actual closed interval [0,2]. Both compiled
conclusions preserve EVERY coordinate x, including interior basepoints.
It also checks radial density of a real closed ball. These examples exercise
nonempty bounded and unbounded carriers; the result statements retain the
model disjunction, while the proof itself branches on boundedness of the
actual distance image. Positive radius is explicit in closed-ball density,
and nontriviality excludes a zero-length interval in global recognition.
The half-interval adapter derives the global metric-endpoint condition;
it does not assume it in that consumer. This is self-review, not human
approval. Endpoint-free line/circle recognition and full AC47 remain open.

```lean
import DifferentialGeometry.Geometry.Comparison.EndpointRecognition
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

private theorem ray_endpoint : ∀ x y : Ici (0 : ℝ),
    dist x (⟨0, by norm_num⟩ : Ici (0 : ℝ)) + dist (⟨0, by norm_num⟩ : Ici (0 : ℝ)) y = dist x y →
      x = ⟨0, by norm_num⟩ ∨ y = ⟨0, by norm_num⟩ := by
  intro x y h
  change |(x : ℝ) - 0| + |0 - (y : ℝ)| = |(x : ℝ) - y| at h
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (show 0 ≤ (x : ℝ) from x.property), abs_of_nonneg (show 0 ≤ (y : ℝ) from y.property)] at h
  rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Or.inl (Subtype.ext (by change (x : ℝ) = 0; linarith))
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at h
    exact Or.inr (Subtype.ext (by change (y : ℝ) = 0; linarith))

example :
    (∃ L : ℝ, 0 < L ∧ ∃ e : Ici (0 : ℝ) ≃ᵢ Icc (0 : ℝ) L,
      ∀ x, (e x : ℝ) = (x : ℝ)) ∨
    (∃ e : Ici (0 : ℝ) ≃ᵢ Ici (0 : ℝ), ∀ x, (e x : ℝ) = (x : ℝ)) := by
  let : CompleteSpace (Ici (0 : ℝ)) := isClosed_Ici.completeSpace_coe
  let : Nontrivial (Ici (0 : ℝ)) := ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
    intro h; have hh := congrArg (fun z : Ici (0 : ℝ) => (z : ℝ)) h; norm_num at hh⟩⟩
  have hdim : dimH (univ : Set (Ici (0 : ℝ))) ≤ 1 := by
    rw [← isometry_subtype_coe.dimH_image]
    exact (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ
  have h := exists_interval_or_ray_isometry_of_endpoint_of_dimH_le_one ray_segments
    (real_comparison.of_isometry isometry_subtype_coe) hdim ray_endpoint
  have hc (x : Ici (0 : ℝ)) : dist (⟨0, by norm_num⟩ : Ici (0 : ℝ)) x = (x : ℝ) := by
    simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (show 0 ≤ (x : ℝ) from x.property)]
  simpa only [hc] using h

example :
    (∃ L : ℝ, 0 < L ∧ ∃ e : Icc (0 : ℝ) 2 ≃ᵢ Icc (0 : ℝ) L,
      ∀ x, (e x : ℝ) = (x : ℝ)) ∨
    (∃ e : Icc (0 : ℝ) 2 ≃ᵢ Ici (0 : ℝ), ∀ x, (e x : ℝ) = (x : ℝ)) := by
  let : CompleteSpace (Icc (0 : ℝ) 2) := isClosed_Icc.completeSpace_coe
  let : Nontrivial (Icc (0 : ℝ) 2) := ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
    intro h; have hh := congrArg (fun z : Icc (0 : ℝ) 2 => (z : ℝ)) h; norm_num at hh⟩⟩
  let p : Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  have hc (x : Icc (0 : ℝ) 2) : dist p x = (x : ℝ) := by
    simp [p, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg x.property.1]
  have hiso : Isometry (fun x : Icc (0 : ℝ) 2 => dist p x) := by
    simpa only [hc] using (isometry_subtype_coe (s := Icc (0 : ℝ) 2))
  have hcurves (x : Icc (0 : ℝ) 2) : ∃ c : unitInterval → Icc (0 : ℝ) 2,
      Continuous c ∧ c 0 = p ∧ c 1 = x := by
    let c : unitInterval → Icc (0 : ℝ) 2 := fun t =>
      ⟨(t : ℝ) * x, mul_nonneg t.property.1 x.property.1,
        (mul_le_mul_of_nonneg_right t.property.2 x.property.1).trans (by simpa using x.property.2)⟩
    exact ⟨c, by fun_prop, by apply Subtype.ext; simp [c, p], by apply Subtype.ext; simp [c]⟩
  simpa only [hc] using exists_interval_or_ray_isometry_of_isometry_dist hcurves hiso

example : (closedBall (0 : ℝ) 1) ⊆ closure (ball (0 : ℝ) 1) :=
  closedBall_subset_closure_ball_of_segments real_segments (by norm_num)

#print axioms isometry_dist_from_endpoint_of_isOpen_segments
#print axioms exists_interval_or_ray_isometry_of_isometry_dist
#print axioms metric_endpoint_of_pointed_half_interval_chart
#print axioms exists_interval_or_ray_isometry_of_half_interval_chart_of_dimH_le_one

```
