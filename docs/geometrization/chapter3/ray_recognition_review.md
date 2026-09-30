# Compiled self-review: global models from an actual ray

Five public theorems and one definition in three leaves add eight owned
declarations including generated proof declarations. The 231-module gate
checks1150 owned declarations (3065 jobs) and all transitive axiom closures;
only propext, Classical.choice and Quot.sound occur. Source-copy
unusedArguments, simpNF and synTaut linters are silent. Declaration kinds
were inspected manually; defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside
these closures. Static audit passes. No full migrated root, fresh blueprint
PDF/Overleaf build, human approval or delegated review is claimed.

The compiled driver checks the actual real ray coordinate at all parameters
and its isometry for every kappa>=0, then the original dimension-one global
recognition consumer on the real line. It separately constructs the actual
closed half-line[-2,infinity), its complete metric, explicit affine segments,
nonnegative comparison and genuine dimension bound by the subtype isometry.
The actual ray starts at0, an interior point. The range theorem is applied
to this space, the impossible onto-line alternative is excluded, and the
returned ray isometry is proved to send the basepoint to EXACTLY2. Its
coordinate is x+2 everywhere. Thus the positive pointed height is checked,
not silently normalized to an endpoint. The original-input recognition
consumer is then applied to this same half-line and actual ray. The final
driver exits zero with only six axiom reports.

Statement review checks the sign convention on the entire ray image,
including its origin, and all four membership cases in the isometry proof.
Outside/outside distances use the same actual opposite point gamma(1).
Completeness enters only the range classification. A lower bound produces
an attained infimum, and absence of a lower bound gives all negative real
values through actual paths and IVT. Both branches produce genuine onto
isometries, not embeddings or homeomorphisms. Recognition preserves every
parameter of the supplied ray. Ray existence and the compact circle branch
remain excluded; no general AC47 completion is claimed.

```lean
import DifferentialGeometry.Geometry.Comparison.RayRecognition
import DifferentialGeometry.Geometry.Comparison.MetricTransfer
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


example (t : Ici (0 : ℝ)) : raySignedDistance real_ray (t : ℝ) = t :=
  raySignedDistance_apply_isometry real_ray_isometry t

example (κ : ℝ) (hκ : 0 ≤ κ) : Isometry (raySignedDistance real_ray) :=
  isometry_raySignedDistance hκ (real_comparison hκ) real_segments real_open_segments real_ray_isometry

example : (∃ e : ℝ ≃ᵢ ℝ, e 0 = 0 ∧ ∀ t : Ici (0 : ℝ), e (t : ℝ) = t) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : ℝ ≃ᵢ Ici (0 : ℝ),
      (e 0 : ℝ) = a ∧ ∀ t : Ici (0 : ℝ), (e (t : ℝ) : ℝ) = (t : ℝ) + a) := by
  exact exists_line_or_ray_isometry_of_isometric_ray_of_dimH_le_one real_segments
    (real_comparison (by norm_num)) (by simp only [Real.dimH_univ]; exact le_rfl) real_ray_isometry

private abbrev H : Type := Ici (-2 : ℝ)
private instance : CompleteSpace H := isClosed_Ici.isComplete.completeSpace_coe
private def hzero : H := ⟨0, by norm_num⟩
private def hray : Ici (0 : ℝ) → H := fun t => ⟨t, le_trans (show (-2 : ℝ) ≤ 0 by norm_num) t.property⟩
private theorem hiso : Isometry (fun t : H => (t : ℝ)) := isometry_subtype_coe
private theorem hray_iso : Isometry hray := Isometry.of_dist_eq (fun _ _ => rfl)
private theorem hsegments (x y : H) :
    ∃ f : unitInterval → H, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → H := fun t => ⟨(1 - (t : ℝ)) * x + (t : ℝ) * y, by
    have hx : -2 ≤ (x : ℝ) := x.property
    have hy : -2 ≤ (y : ℝ) := y.property
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    change (-2 : ℝ) ≤ (1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ)
    nlinarith⟩
  refine ⟨f, by fun_prop, ?_, ?_, ?_⟩
  · apply Subtype.ext; simp [f]
  · apply Subtype.ext; simp [f]
  · intro s t
    change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
      |(x : ℝ) - y| * |(s : ℝ) - t|
    rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
      ((y : ℝ) - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm (y : ℝ) (x : ℝ)]

private theorem hcurves (x : H) : ∃ c : unitInterval → H,
    Continuous c ∧ c 0 = hzero ∧ c 1 = x := by
  obtain ⟨c, hc, h0, h1, _⟩ := hsegments hzero x
  exact ⟨c, hc, h0, h1⟩

example : ∃ e : H ≃ᵢ Ici (0 : ℝ), (e hzero : ℝ) = 2 ∧
    ∀ x, (e x : ℝ) = (x : ℝ) + 2 := by
  have hrange : Ici (0 : ℝ) ⊆ range (fun t : H => (t : ℝ)) := by
    intro t ht
    exact ⟨⟨t, le_trans (show (-2 : ℝ) ≤ 0 by norm_num) ht⟩, rfl⟩
  rcases exists_line_or_ray_isometry_of_isometry_range hiso (show (hzero : ℝ) = 0 from rfl)
      hrange hcurves with ⟨e, _, he⟩ | ⟨a, _, e, he0, he⟩
  · obtain ⟨x, hx⟩ := e.surjective (-3)
    have hx2 : -2 ≤ (x : ℝ) := x.property
    rw [he] at hx
    linarith
  · have hlo : 0 ≤ (-2 : ℝ) + a := by
      have ht : 0 ≤ (e ⟨-2, by norm_num⟩ : ℝ) := (e ⟨-2, by norm_num⟩).property
      rwa [he] at ht
    obtain ⟨x, hx⟩ := e.surjective ⟨0, by simp⟩
    have hx0 := congrArg (fun z : Ici (0 : ℝ) => (z : ℝ)) hx
    rw [he] at hx0
    have hx2 : -2 ≤ (x : ℝ) := x.property
    have ha2 : a = 2 := by change (x : ℝ) + a = 0 at hx0; linarith
    exact ⟨e, ha2 ▸ he0, fun x => ha2 ▸ he x⟩

private theorem hcomparison : fourPointComparison 0 (univ : Set H) := by
  apply (fourPointComparison_image_iff_of_dist_eq
    (f := fun x : H => (x : ℝ)) (s := univ) (fun _ _ _ _ => rfl)).mp
  exact (real_comparison (by norm_num)).mono (subset_univ _)

private theorem hdimension : dimH (univ : Set H) ≤ 1 := by
  rw [← hiso.dimH_image]
  calc
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = 1 := Real.dimH_univ

example : (∃ e : H ≃ᵢ ℝ, e hzero = 0 ∧ ∀ t, e (hray t) = (t : ℝ)) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : H ≃ᵢ Ici (0 : ℝ),
      (e hzero : ℝ) = a ∧ ∀ t, (e (hray t) : ℝ) = (t : ℝ) + a) :=
  exists_line_or_ray_isometry_of_isometric_ray_of_dimH_le_one
    hsegments hcomparison hdimension hray_iso

#print axioms raySignedDistance
#print axioms raySignedDistance_apply_isometry
#print axioms isometry_raySignedDistance
#print axioms Metric.exists_line_or_ray_isometry_of_isometry_range
#print axioms exists_line_or_ray_isometry_of_isometric_ray_of_open_segments
#print axioms exists_line_or_ray_isometry_of_isometric_ray_of_dimH_le_one
```
