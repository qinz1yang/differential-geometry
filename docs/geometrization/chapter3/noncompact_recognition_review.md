# Compiled self-review: noncompact one-dimensional recognition

Four public theorems in three leaves add five owned declarations, including
a generated proof declaration. The234-module gate checks1155 owned
declarations (3068 jobs) with all transitive axiom closures limited to
propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were inspected
manually; defLemma is unavailable. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning remains outside these closures.
Static audit passes. No migrated full-root, fresh blueprint PDF/Overleaf
build, human or delegated review is claimed.

The compiled driver proves actual noncompactness of the real line and of
the complete half-line[-2,infinity), constructs explicit minimizing curves,
checks actual comparison and dimension, and invokes the ray producer at
every real point and at the interior basepoint0 of the half-line. Properness
of the latter is produced by the new theorem in the ray example. The
properness theorem is separately checked for every kappa>=0 with actual
local real comparison. Both the length-input and segment-input original
recognition consumers are applied. Earlier signed-coordinate and exact
positive-height2 examples are retained in the same driver. It compiles
with only four axiom reports.

The ray proof uses one fixed ultrafilter refining the natural tail for every
real parameter. The chosen pointwise limits are therefore compatible; for
each pair their exact distance is the limit of an eventually constant
sequence. Compactness is used only on actual finite-radius closed balls.
The basepoint comes from the radius0 ball. Curvature and dimension are
absent from this general metric theorem. Noncompactness supplies unbounded
endpoints via compact closed balls; no unproved ray-extension or uniqueness
claim appears. The properness theorem derives local compactness internally
at arbitrary nonnegative parameter and any finite natural dimension bound.
The recognition theorem derives its minimizing segments, ray and open
segment interiors, and concludes actual onto isometries with the ray's
pointed height retained. Only the noncompact AC47 branch is completed.
The compact circle branch, full AC48 and Chapters3-4 remain unfinished.

```lean
import DifferentialGeometry.Geometry.Comparison.NoncompactRecognition
import Mathlib.Topology.Order.Compact
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


private theorem real_noncompact : ¬ IsCompact (univ : Set ℝ) := by
  intro h
  exact not_bddAbove_univ h.bddAbove

example (p : ℝ) : ∃ r : Ici (0 : ℝ) → ℝ, Isometry r ∧ r ⟨0, by simp⟩ = p :=
  exists_isometric_ray_of_not_isCompact real_segments real_noncompact p

example (κ : ℝ) (hκ : 0 ≤ κ) : ProperSpace ℝ :=
  properSpace_of_local_comparison_and_dimH real_curves hκ (n := 1)
    (by simp only [Real.dimH_univ, Nat.cast_one]; exact le_rfl)
    (fun p => ambient_local p hκ)

example (p : ℝ) : (∃ e : ℝ ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : ℝ ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) :=
  exists_line_or_ray_isometry_of_not_isCompact_of_dimH_le_one real_curves
    (real_comparison (by norm_num)) (by simp only [Real.dimH_univ]; exact le_rfl)
    real_noncompact p

private theorem hnoncompact : ¬ IsCompact (univ : Set H) := by
  intro h
  obtain ⟨M, hM⟩ := (h.image hiso.continuous).bddAbove
  let x : H := ⟨max M (-2) + 1, by
    change (-2 : ℝ) ≤ max M (-2) + 1
    linarith [le_max_right M (-2)]⟩
  have hx := hM ⟨x, mem_univ x, rfl⟩
  change max M (-2) + 1 ≤ M at hx
  linarith [le_max_left M (-2)]

example : ∃ r : Ici (0 : ℝ) → H, Isometry r ∧ r ⟨0, by simp⟩ = hzero := by
  let : ProperSpace H := properSpace_of_local_comparison_and_dimH
    (arbitrarily_short_curves_of_metric_segments hsegments) (le_refl (0 : ℝ))
    (n := 1) (by simpa using hdimension)
    (fun p => ⟨univ, isOpen_univ, hcomparison, mem_univ p⟩)
  exact exists_isometric_ray_of_not_isCompact hsegments hnoncompact hzero

example : (∃ e : H ≃ᵢ ℝ, e hzero = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : H ≃ᵢ Ici (0 : ℝ), (e hzero : ℝ) = a) :=
  exists_line_or_ray_isometry_of_not_isCompact_of_geodesic_dimH_le_one
    hsegments hcomparison hdimension hnoncompact hzero

#print axioms Metric.exists_isometric_ray_of_not_isCompact
#print axioms properSpace_of_local_comparison_and_dimH
#print axioms exists_line_or_ray_isometry_of_not_isCompact_of_dimH_le_one
#print axioms exists_line_or_ray_isometry_of_not_isCompact_of_geodesic_dimH_le_one
```
