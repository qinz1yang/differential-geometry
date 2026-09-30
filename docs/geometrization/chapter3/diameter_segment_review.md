# Compiled self-review: exterior distances at a diameter segment

Five public theorems in three leaves add five owned declarations. The
239-module gate checks1163 owned declarations (3073 jobs), including all
transitive axiom closures; only propext, Classical.choice and Quot.sound
occur. Source-copy unusedArguments, simpNF and synTaut linters are silent.
Declaration kinds were inspected manually; defLemma is unavailable.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier
warning remains outside these closures. Static audit passes; no migrated
full-root, fresh blueprint PDF/Overleaf build, human or delegated review
is claimed.

The compiled driver uses Mathlib's ACTUAL normed quotient AddCircle4,
not a placeholder circle type or an assumed metric packet. It constructs
explicit minimizing curves from representatives in[-2,2], proves the
semicircle[0,2] isometric with open interior, proves the global diameter
bound2 and nontriviality, and checks that every representative in(2,4)
lies outside the entire semicircle range. Four-point nonnegative comparison
is proved for this real circle: among three centered representatives two
lie on the same side, giving zero model angle; the other angles are<=pi.
All required geometry is thus supplied by actual inhabited proofs.

The exterior-distance theorem is checked on ALL these exterior points and
ALL segment parameters, including endpoints. The diameter-additivity theorem
is checked on the same circle, and the exterior pair theorem on the actual
distinct points3 and7/2. The diameter-segment producer is invoked on this
compact nontrivial circle. An actual minimizing curve from1 to3 is proved
to pass through a semicircle endpoint. A separate real example checks the
D=0 exterior-distance case. The final driver exits zero with five axiom
reports. Diagnostic draft elaboration timeouts caused by mistakenly typed
circle numerals were repaired by explicit real-to-quotient casts; no
heartbeat limit or proof-integrity setting was changed.

Mathlib bodies checked for the review: Analysis/Normed/Group/AddCircle.lean
40-43,66-137 (actual quotient norm, norm_coe_eq_abs_iff and half-period bound),
Topology/Instances/AddCircle/Defs.lean205-229,301-306,461-476 (quotient map,
period identity and representative intervals), and Topology/Algebra/Group/
Quotient.lean43-52 (continuous/open quotient map), at pinned c55e6e786f49.
These support the review example, not extra public theorem assumptions.

Statement review checks preconnectedness of the actual curve domain,
closedness of the finite segment image, explicit interior openness, and
exclusion from the ENTIRE range. The minimum formula includes both endpoints
and zero length. Diameter hypotheses bound every pair, not only distance
from one center. The balanced parameter is proved to belong to[0,D].
The exterior pair theorem uses an actual common opposite point at positive
parameter, with positivity derived from the endpoint exclusions. None of
these lemmas presupposes a second arc or a circle. Those constructions remain.

```lean
import DifferentialGeometry.Topology.MetricSpace.RayExteriorDistance
import DifferentialGeometry.Geometry.Comparison.CommonOpposite
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalCovering
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic
import DifferentialGeometry.Geometry.Comparison.DiameterSegment
import DifferentialGeometry.Topology.MetricSpace.DiameterSegmentExistence
import Mathlib.Analysis.Normed.Group.AddCircle
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Tactic

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

private abbrev C := AddCircle (4 : ℝ)
private instance : Fact (0 < (4 : ℝ)) := ⟨by norm_num⟩

private theorem cnorm (a : ℝ) (ha : |a| ≤ 2) : ‖(a : C)‖ = |a| := by
  exact (AddCircle.norm_coe_eq_abs_iff 4 (by norm_num)).mpr (by norm_num; exact ha)

private theorem cdist (a b : ℝ) (hab : |a - b| ≤ 2) :
    dist (a : C) (b : C) = |a - b| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact cnorm _ hab

private theorem crep (x : C) : ∃ a ∈ Icc (-2 : ℝ) 2, (a : C) = x := by
  have h : x ∈ ((↑) : ℝ → C) '' Icc (-2 : ℝ) (-2 + 4) := by
    rw [AddCircle.coe_image_Icc_eq]
    exact mem_univ x
  norm_num at h
  exact h

private theorem csegments (x y : C) :
    ∃ f : unitInterval → C, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  obtain ⟨a, ha, hrep⟩ := crep (y - x)
  have ha2 : |a| ≤ 2 := abs_le.mpr ⟨ha.1, ha.2⟩
  have hxy : dist x y = |a| := by
    rw [dist_comm, dist_eq_norm, ← hrep]
    exact cnorm a ha2
  let f : unitInterval → C := fun t => x + (((t : ℝ) * a : ℝ) : C)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.add (QuotientAddGroup.continuous_mk.comp (continuous_subtype_val.mul_const a))
  · simp [f]
  · simpa [f] using congrArg (fun z : C => x + z) hrep
  · intro s t
    have hst : |(s : ℝ) - t| ≤ 1 := abs_le.mpr
      ⟨by linarith [s.property.1, t.property.2], by linarith [s.property.2, t.property.1]⟩
    change dist (x + (((s : ℝ) * a : ℝ) : C)) (x + (((t : ℝ) * a : ℝ) : C)) = _
    rw [dist_add_left]
    rw [cdist _ _ (by rw [← sub_mul, abs_mul]; nlinarith [abs_nonneg ((s : ℝ) - t), abs_nonneg a]),
      ← sub_mul, abs_mul, hxy]
    exact mul_comm _ _

private def csegment : Icc (0 : ℝ) 2 → C := fun t => (t : ℝ)
private theorem csegment_iso : Isometry csegment := by
  apply Isometry.of_dist_eq
  intro s t
  exact cdist s t (abs_le.mpr
    ⟨by linarith [s.property.1, t.property.2], by linarith [s.property.2, t.property.1]⟩)

private theorem csegment_open : IsOpen (csegment '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 2}) := by
  have heq : csegment '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 2} =
      ((↑) : ℝ → C) '' Ioo (0 : ℝ) 2 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  rw [heq]
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

private theorem cdiam (x y : C) : dist x y ≤ 2 := by
  rw [dist_eq_norm]
  convert (AddCircle.norm_le_half_period (p := (4 : ℝ)) (x := x - y) (by norm_num)) using 1; norm_num

private theorem coutside : (3 : ℝ) ∈ Ioo (2 : ℝ) 4 := by norm_num

private theorem cnot (a : ℝ) (ha : a ∈ Ioo (2 : ℝ) 4) : (a : C) ∉ range csegment := by
  rintro ⟨t, ht⟩
  have hperiod : ∃ n : ℤ, (n : ℝ) * 4 = (t : ℝ) - a := by
    have hz : (((t : ℝ) - a : ℝ) : C) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr ht
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (4 : ℝ)).mp hz
    exact ⟨n, by simpa only [zsmul_eq_mul] using hn⟩
  obtain ⟨n, hn⟩ := hperiod
  have hnlo : (-1 : ℝ) < n := by linarith [t.property.1, ha.2]
  have hnhi : (n : ℝ) < 0 := by linarith [t.property.2, ha.1]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < 0 := by exact_mod_cast hnhi
  omega

private theorem csame (p : C) {a b : ℝ} (ha : a ∈ Icc (-2 : ℝ) 2)
    (hb : b ∈ Icc (-2 : ℝ) 2)
    (hs : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0))
    (hap : p + (a : C) ≠ p) (hbp : p + (b : C) ≠ p) :
    comparisonAngleNegCurvature 0 (dist p (p + (a : C))) (dist p (p + (b : C)))
      (dist (p + (a : C)) (p + (b : C))) = 0 := by
  have heq : dist (p + (a : C)) (p + (b : C)) =
      |dist p (p + (a : C)) - dist p (p + (b : C))| := by
    have hnorm (r : ℝ) (hr : r ∈ Icc (-2 : ℝ) 2) : dist p (p + (r : C)) = |r| := by
      rw [dist_eq_norm, show p - (p + (r : C)) = -(r : C) by abel, norm_neg]
      exact cnorm _ (abs_le.mpr hr)
    rw [hnorm a ha, hnorm b hb, dist_add_left]
    rcases hs with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
    · rw [cdist _ _ (abs_le.mpr ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩),
        abs_of_nonneg ha0, abs_of_nonneg hb0]
    · rw [cdist _ _ (abs_le.mpr ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩),
        abs_of_nonpos ha0, abs_of_nonpos hb0, neg_sub_neg, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub le_rfl (dist_pos.mpr (Ne.symm hap))
    (dist_pos.mpr (Ne.symm hbp))

private theorem ccomparison : fourPointComparison 0 (univ : Set C) := by
  intro p _ a _ b _ c _ hap hbp hcp
  obtain ⟨ra, hra, ha⟩ := crep (a - p)
  obtain ⟨rb, hrb, hb⟩ := crep (b - p)
  obtain ⟨rc, hrc, hc⟩ := crep (c - p)
  have ha' : p + (ra : C) = a := by rw [ha]; abel
  have hb' : p + (rb : C) = b := by rw [hb]; abel
  have hc' : p + (rc : C) = c := by rw [hc]; abel
  have hab := (comparisonAngleNegCurvature_mem_Icc 0 (dist p a) (dist p b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 0 (dist p b) (dist p c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 0 (dist p c) (dist p a) (dist c a)).2
  have hzero_ab (hs : (0 ≤ ra ∧ 0 ≤ rb) ∨ (ra ≤ 0 ∧ rb ≤ 0)) :
      comparisonAngleNegCurvature 0 (dist p a) (dist p b) (dist a b) = 0 := by
    simpa only [ha', hb'] using csame p hra hrb hs (ha' ▸ hap) (hb' ▸ hbp)
  have hzero_bc (hs : (0 ≤ rb ∧ 0 ≤ rc) ∨ (rb ≤ 0 ∧ rc ≤ 0)) :
      comparisonAngleNegCurvature 0 (dist p b) (dist p c) (dist b c) = 0 := by
    simpa only [hb', hc'] using csame p hrb hrc hs (hb' ▸ hbp) (hc' ▸ hcp)
  have hzero_ca (hs : (0 ≤ rc ∧ 0 ≤ ra) ∨ (rc ≤ 0 ∧ ra ≤ 0)) :
      comparisonAngleNegCurvature 0 (dist p c) (dist p a) (dist c a) = 0 := by
    simpa only [hc', ha'] using csame p hrc hra hs (hc' ▸ hcp) (ha' ▸ hap)
  rcases le_total 0 ra with har | har <;> rcases le_total 0 rb with hbr | hbr <;>
    rcases le_total 0 rc with hcr | hcr
  all_goals first
    | have hz := hzero_ab (Or.inl ⟨har, hbr⟩); linarith
    | have hz := hzero_ab (Or.inr ⟨har, hbr⟩); linarith
    | have hz := hzero_bc (Or.inl ⟨hbr, hcr⟩); linarith
    | have hz := hzero_bc (Or.inr ⟨hbr, hcr⟩); linarith
    | have hz := hzero_ca (Or.inl ⟨hcr, har⟩); linarith
    | have hz := hzero_ca (Or.inr ⟨hcr, har⟩); linarith
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


private instance : Nontrivial C := ⟨⟨((0 : ℝ) : C), ((1 : ℝ) : C), by
  intro h
  have hd := cdist 0 1 (by norm_num)
  rw [h, dist_self] at hd
  norm_num at hd⟩⟩

example {a : ℝ} (ha : a ∈ Ioo (2 : ℝ) 4) (t : Icc (0 : ℝ) 2) :
    dist (a : C) (csegment t) = min (dist (a : C) (0 : C) + (t : ℝ))
      (dist (a : C) ((2 : ℝ) : C) + (2 - (t : ℝ))) :=
  dist_to_segment_of_not_mem_range csegments (by norm_num) csegment_iso csegment_open (cnot a ha) t

example {a : ℝ} (ha : a ∈ Ioo (2 : ℝ) 4) :
    dist (a : C) (0 : C) + dist (a : C) ((2 : ℝ) : C) = 2 :=
  dist_add_dist_eq_of_outside_diameter_segment csegments (by norm_num)
    csegment_iso csegment_open cdiam (cnot a ha)

example : dist ((3 : ℝ) : C) ((7 / 2 : ℝ) : C) =
    |dist ((3 : ℝ) : C) (0 : C) - dist ((7 / 2 : ℝ) : C) (0 : C)| :=
  dist_eq_abs_sub_of_outside_diameter_segment (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso csegment_open cdiam (cnot 3 (by norm_num)) (cnot (7/2) (by norm_num))

example : ∃ D : ℝ, 0 < D ∧ ∃ σ : Icc (0 : ℝ) D → C,
    Isometry σ ∧ ∀ x y : C, dist x y ≤ D :=
  exists_diameter_isometric_segment csegments

example : ∃ f : unitInterval → C, Continuous f ∧ f 0 = ((1 : ℝ) : C) ∧
    f 1 = ((3 : ℝ) : C) ∧ ∃ t, f t = (0 : C) ∨ f t = ((2 : ℝ) : C) := by
  obtain ⟨f, hf, hf0, hf1, _⟩ := csegments ((1 : ℝ) : C) ((3 : ℝ) : C)
  refine ⟨f, hf, hf0, hf1, ?_⟩
  exact exists_segment_endpoint_on_curve_of_exit (by norm_num) csegment_iso csegment_open hf
    ⟨((1 : ℝ) : C), ⟨0, hf0⟩, ⟨1, by norm_num⟩, by norm_num, rfl⟩
    ⟨1, hf1 ▸ cnot 3 (by norm_num)⟩

example : dist (1 : ℝ) 0 = min (dist (1 : ℝ) 0 + 0) (dist (1 : ℝ) 0 + (0 - 0)) := by
  let σ : Icc (0 : ℝ) 0 → ℝ := Subtype.val
  have hσ : Isometry σ := isometry_subtype_coe
  apply dist_to_segment_of_not_mem_range real_segments (le_refl (0 : ℝ)) hσ
    (real_open_segments 0 0 σ hσ) (t := ⟨0, by norm_num⟩)
  rintro ⟨s, hs⟩
  have hs0 : (s : ℝ) ≤ 0 := s.property.2
  change (s : ℝ) = 1 at hs
  linarith

#print axioms Metric.exists_segment_endpoint_on_curve_of_exit
#print axioms Metric.dist_to_segment_of_not_mem_range
#print axioms Metric.dist_add_dist_eq_of_outside_diameter_segment
#print axioms dist_eq_abs_sub_of_outside_diameter_segment
#print axioms Metric.exists_diameter_isometric_segment
```
