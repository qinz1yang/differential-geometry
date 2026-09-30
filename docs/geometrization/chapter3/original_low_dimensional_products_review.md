# Compiled self-review: original-global AC45/AC48 assembly

Seven public theorems in four leaves add eight owned declarations, including
a generated proof declaration. The 253-module gate checks 1192 owned
declarations (3087 jobs), and every transitive axiom closure uses only
propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually
inspected; defLemma is unavailable. Earlier leaves are unchanged. The inherited
AreaUpperBarrier warning remains outside these closures. Static audit passes.
No full migrated root, fresh blueprint PDF/Overleaf, human or delegated review
is claimed.

The compiled driver retains the genuine circle, line, ray, segment and singleton
geometry and same-constructed-limit integration from the preceding review.
New tests produce the exact C_R net bound on the actual AddCircle4 for every
positive R and 0<epsilon<=1, and polynomial nets on the actual singleton.
An actual zero-Euclidean-factor splitting of the circle exercises the original
rank/dimension theorem and the global product alternatives. A genuine positive-
rank splitting of R is constructed with its actual orthonormal one-dimensional
basis and a singleton factor; the original full-rank theorem returns a pointed
onto Euclidean isometry. An actual real splitting of R tests the dimension<=2
product theorem at every basepoint. The identity line in R independently tests
the specified-line theorem, retaining its canonical coordinate. These are
concrete non-vacuous applications, not assumptions of the requested output.
The driver exits zero and prints seven axiom reports. It does not separately
instantiate the full-rank theorem on a two-dimensional plane; the checked
public proof quantifies over every n>=1, including n=2.

Statement audit checks the exact polynomial constant and epsilon quantifiers,
original metric length and global comparison, ambient Hausdorff dimension,
actual onto splitting and chosen basepoint. Factor dimension and covering are
produced, never assumed in the original-global consumers. The rank bound is
proved rather than inferred from natural subtraction; full-rank recognition
has the actual pointed zero-coordinate condition. Product outputs preserve
all first coordinates and retain interior transverse heights. R x_2 R uses
the standard Pythagorean product metric, and the circle uses its existing
normed quotient. The specified-line theorem invokes accepted AC43 on global
proper geometry and retains the actual lineCoordinate at every point. No
line is inferred from convergence or a ray. Uniqueness/maximality and smooth
structure are not consequences asserted here.

```lean
import DifferentialGeometry.Geometry.Comparison.LineProductModels
import DifferentialGeometry.Geometry.Metric.Approximation.FactorGlobalModels
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Comparison.GlobalOneDimensionalModels
import DifferentialGeometry.Geometry.Comparison.DiameterCircleIsometry
import DifferentialGeometry.Geometry.Comparison.OppositeDiameterArc
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


private def copposite : Icc (0 : ℝ) 2 → C := fun t => -csegment t
private theorem copposite_iso : Isometry copposite := isometry_neg.comp csegment_iso
private theorem copposite_zero : copposite ⟨0, by norm_num⟩ = csegment ⟨0, by norm_num⟩ := by
  change -(0 : C) = 0
  simp
private theorem copposite_end : copposite ⟨2, by norm_num⟩ = csegment ⟨2, by norm_num⟩ := by
  change -((2 : ℝ) : C) = ((2 : ℝ) : C)
  rw [← AddCircle.coe_neg]
  rw [show (-2 : ℝ) = 2 - 4 by norm_num, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
private theorem copposite_one : copposite ⟨1, by norm_num⟩ = ((3 : ℝ) : C) := by
  change -((1 : ℝ) : C) = ((3 : ℝ) : C)
  rw [← AddCircle.coe_neg]
  have h := AddCircle.coe_add_period (4 : ℝ) (-1)
  norm_num at h
  exact h.symm
private theorem copposite_out (t : Icc (0 : ℝ) 2) (ht0 : 0 < (t : ℝ)) (ht2 : (t : ℝ) < 2) :
    copposite t ∉ range csegment :=
  segment_interior_outside_of_point_outside (by norm_num) csegment_iso copposite_iso csegment_open
    copposite_zero copposite_end (copposite_one ▸ cnot 3 (by norm_num)) t ht0 ht2

example (x : C) : x ∈ range csegment ∨ x ∈ range copposite :=
  mem_range_or_mem_range_of_opposite_diameter_arcs (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso copposite_iso csegment_open cdiam copposite_zero copposite_out x

example : ∃ τ : Icc (0 : ℝ) 2 → C, Isometry τ ∧
    τ ⟨0, by norm_num⟩ = (0 : C) ∧ τ ⟨2, by norm_num⟩ = ((2 : ℝ) : C) ∧
    ((3 : ℝ) : C) ∈ range τ ∧
    (∀ t : Icc (0 : ℝ) 2, 0 < (t : ℝ) → (t : ℝ) < 2 → τ t ∉ range csegment) ∧
    ∀ y : C, y ∈ range csegment ∨ y ∈ range τ :=
  exists_opposite_diameter_arc_of_point_outside (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso csegment_open cdiam (cnot 3 (by norm_num))

example : ∃ σ : Icc (0 : ℝ) (dist (0 : ℝ) 2) → ℝ, Isometry σ ∧
    σ ⟨0, le_rfl, dist_nonneg⟩ = 0 ∧ σ ⟨dist (0 : ℝ) 2, dist_nonneg, le_rfl⟩ = 2 ∧
    σ ⟨dist (0 : ℝ) 1, dist_nonneg, by norm_num [Real.dist_eq]⟩ = 1 :=
  exists_isometric_segment_through_of_dist_add_eq real_segments (by norm_num [Real.dist_eq])

example : ∃ σ : Icc (0 : ℝ) (dist (1 : ℝ) 1) → ℝ, Isometry σ ∧
    σ ⟨0, le_rfl, dist_nonneg⟩ = 1 ∧ σ ⟨dist (1 : ℝ) 1, dist_nonneg, le_rfl⟩ = 1 ∧
    σ ⟨dist (1 : ℝ) 1, dist_nonneg, le_rfl⟩ = 1 :=
  exists_isometric_segment_through_of_dist_add_eq real_segments (by simp)


example (L : ℝ) (hL : 0 < L) : ‖(L : AddCircle L)‖ = min L (L - L) :=
  AddCircle.norm_coe_eq_min_of_mem_Icc hL ⟨hL.le, le_rfl⟩

example (L : ℝ) (hL : 0 < L) : ‖((L / 2 : ℝ) : AddCircle L)‖ = L / 2 := by
  rw [AddCircle.norm_coe_eq_min_of_mem_Icc hL (by constructor <;> linarith)]
  rw [show L - L / 2 = L / 2 by ring, min_self]

example : dist ((0 : ℝ) : C) ((2 : ℝ) : C) = 2 := by
  rw [AddCircle.dist_coe_eq_abs_of_le_half_period (by norm_num : 0 < (4 : ℝ)) (by norm_num)]
  norm_num

example (t : Icc (0 : ℝ) 2) : diameterCircleCoordinate (by norm_num) csegment (csegment t) =
    ((t : ℝ) : AddCircle ((2 : ℝ) * 2)) :=
  diameterCircleCoordinate_apply_isometry (by norm_num) csegment_iso t

example : Isometry (diameterCircleCoordinate (by norm_num : 0 < (2 : ℝ)) csegment) :=
  isometry_diameterCircleCoordinate (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso csegment_open cdiam

example (t : Icc (0 : ℝ) 2) : diameterCircleCoordinate (by norm_num) csegment (copposite t) =
    ((-(t : ℝ) : ℝ) : AddCircle ((2 : ℝ) * 2)) :=
  diameterCircleCoordinate_on_opposite_arc (by norm_num) csegment_iso copposite_iso
    copposite_zero copposite_end copposite_out t

example : ∃ e : C ≃ᵢ AddCircle ((2 : ℝ) * 2),
    (∀ t, e (csegment t) = ((t : ℝ) : AddCircle ((2 : ℝ) * 2))) ∧
    (∀ t, e (copposite t) = ((-(t : ℝ) : ℝ) : AddCircle ((2 : ℝ) * 2))) :=
  exists_circle_isometry_of_opposite_diameter_arcs (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso copposite_iso csegment_open cdiam
    copposite_zero copposite_end copposite_out

example : ∃ e : C ≃ᵢ AddCircle ((2 : ℝ) * 2),
    ∀ t, e (csegment t) = ((t : ℝ) : AddCircle ((2 : ℝ) * 2)) :=
  exists_circle_isometry_of_outside_diameter_segment (le_refl (0 : ℝ)) ccomparison csegments
    (by norm_num) csegment_iso csegment_open cdiam (cnot 3 (by norm_num))


private theorem cdimension : dimH (univ : Set C) ≤ 1 := by
  have hl : LipschitzWith 1 (fun a : ℝ => (a : C)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [NNReal.coe_one, one_mul, dist_eq_norm, ← AddCircle.coe_sub, Real.dist_eq]
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (4 : ℝ)) (m := a - b))
  have hr : range (fun a : ℝ => (a : C)) = univ := by
    apply range_eq_univ.mpr
    intro x
    obtain ⟨a, _, ha⟩ := crep x
    exact ⟨a, ha⟩
  have hd := hl.dimH_range_le
  rwa [hr, Real.dimH_univ] at hd

private def modelConclusion (T : Type*) [MetricSpace T] (p : T) : Prop :=
    (∃ e : T ≃ᵢ EuclideanSpace ℝ (Fin 0), e p = 0) ∨
    (∃ e : T ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : T ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : T ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : T ≃ᵢ AddCircle L, e p = 0)

example (p : C) :
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : C ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : C ≃ᵢ AddCircle L, e p = 0) :=
  exists_interval_or_circle_isometry_of_compact_dimH_le_one csegments ccomparison cdimension p

example (p : C) : modelConclusion C p :=
  exists_pointed_one_dimensional_model (arbitrarily_short_curves_of_metric_segments csegments)
    ccomparison cdimension p

example (p : ℝ) : modelConclusion ℝ p :=
  exists_pointed_one_dimensional_model real_curves (real_comparison (by norm_num))
    (by simp only [Real.dimH_univ]; exact le_rfl) p

private abbrev Z0 := EuclideanSpace ℝ (Fin 0)
private theorem zsegments (x y : Z0) : ∃ f : unitInterval → Z0,
    Continuous f ∧ f 0 = x ∧ f 1 = y ∧ ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun _ => x, continuous_const, rfl, Subsingleton.elim _ _, ?_⟩
  intro s t
  simp only [Subsingleton.elim x y, dist_self, zero_mul]
private theorem zcomparison : fourPointComparison 0 (univ : Set Z0) := by
  intro p _ a _ _ _ _ _ hap
  exact (hap (Subsingleton.elim a p)).elim
private theorem zdimension : dimH (univ : Set Z0) ≤ 1 := by
  rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
  norm_num
example : modelConclusion Z0 0 :=
  exists_pointed_one_dimensional_model (arbitrarily_short_curves_of_metric_segments zsegments)
    zcomparison zdimension 0
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

private theorem hcomparison : fourPointComparison 0 (univ : Set H) := by
  apply (fourPointComparison_image_iff_of_dist_eq
    (f := fun x : H => (x : ℝ)) (s := univ) (fun _ _ _ _ => rfl)).mp
  exact (real_comparison (by norm_num)).mono (subset_univ _)

private theorem hdimension : dimH (univ : Set H) ≤ 1 := by
  rw [← hiso.dimH_image]
  calc
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = 1 := Real.dimH_univ


example : modelConclusion H hzero :=
  exists_pointed_one_dimensional_model (arbitrarily_short_curves_of_metric_segments hsegments)
    hcomparison hdimension hzero

private abbrev J : Type := Icc (-2 : ℝ) 3
private instance : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
private instance : Nontrivial J := ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
  intro h
  have hh := congrArg (fun t : J => (t : ℝ)) h
  norm_num at hh⟩⟩
private theorem jsegments (x y : J) : ∃ f : unitInterval → J,
    Continuous f ∧ f 0 = x ∧ f 1 = y ∧ ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → J := fun t => ⟨(1 - (t : ℝ)) * x + (t : ℝ) * y, by
    change (1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ) ∈ Icc (-2 : ℝ) 3
    constructor <;> nlinarith [x.property.1, x.property.2, y.property.1, y.property.2,
      t.property.1, t.property.2]⟩
  refine ⟨f, by fun_prop, ?_, ?_, ?_⟩
  · apply Subtype.ext; simp [f]
  · apply Subtype.ext; simp [f]
  · intro s t
    change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
      |(x : ℝ) - y| * |(s : ℝ) - t|
    rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
      ((y : ℝ) - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm (y : ℝ) (x : ℝ)]
private theorem jcomparison : fourPointComparison 0 (univ : Set J) := by
  apply (fourPointComparison_image_iff_of_dist_eq
    (f := fun x : J => (x : ℝ)) (s := univ) (fun _ _ _ _ => rfl)).mp
  exact (real_comparison (by norm_num)).mono (subset_univ _)
private theorem jdimension : dimH (univ : Set J) ≤ 1 := by
  have hi : Isometry (fun t : J => (t : ℝ)) := isometry_subtype_coe
  rw [← hi.dimH_image]
  exact (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ
example : modelConclusion J ⟨0, by norm_num⟩ :=
  exists_pointed_one_dimensional_model (arbitrarily_short_curves_of_metric_segments jsegments)
    jcomparison jdimension ⟨0, by norm_num⟩


open Filter GC.MetricGeometry
open scoped Topology
private noncomputable def kappas (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)
private def radii (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem kappas_pos (i : ℕ) : 0 < kappas i := by dsimp [kappas]; positivity
private theorem kappas_zero : Tendsto kappas atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
private theorem radii_pos (i : ℕ) : 0 < radii i := by dsimp [radii]; positivity
private theorem radii_top : Tendsto radii atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with i hi
  have hNi : (N : ℝ) ≤ i := by exact_mod_cast hi
  dsimp [radii]
  linarith

private theorem real_dim (i : ℕ) : dimH (ball (0 : ℝ) (radii i)) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using
    (dimH_mono (subset_univ (ball (0 : ℝ) (radii i)))).trans_eq Real.dimH_univ


private noncomputable def zero_split {T : Type*} [MetricSpace T] :
    T ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × T) := by
  let f : T → WithLp 2 (EuclideanSpace ℝ (Fin 0) × T) := fun x => WithLp.toLp 2 (0, x)
  have hf : Isometry f := WithLp.isometry_prodMk_left 0
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨y.snd, ?_⟩
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (Subsingleton.elim _ _) rfl
  exact ⟨Equiv.ofBijective f ⟨hf.injective, hsurj⟩, hf⟩


private def productConclusion (T E Z : Type*) [MetricSpace T] [MetricSpace E] [MetricSpace Z]
    (p : T) (e : T ≃ᵢ WithLp 2 (E × Z)) : Prop :=
    (∃ F : T ≃ᵢ E, ∀ x, F x = (e x).fst) ∨
    (∃ F : T ≃ᵢ WithLp 2 (E × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : T ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : T ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : T ≃ᵢ WithLp 2 (E × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst)

example : productConclusion C Z0 C (((1 : ℝ) : C)) zero_split :=
  zero_split.exists_product_model_of_dimH_factor_le_one
    csegments ccomparison cdimension (((1 : ℝ) : C))

example : productConclusion J Z0 J (⟨0, by norm_num⟩) zero_split :=
  zero_split.exists_product_model_of_dimH_factor_le_one
    jsegments jcomparison jdimension (⟨0, by norm_num⟩)

example : productConclusion H Z0 H (hzero) zero_split :=
  zero_split.exists_product_model_of_dimH_factor_le_one
    hsegments hcomparison hdimension (hzero)

example : productConclusion ℝ Z0 ℝ (0) zero_split :=
  zero_split.exists_product_model_of_dimH_factor_le_one
    real_segments (real_comparison (by norm_num)) (by simp only [Real.dimH_univ]; exact le_rfl) (0)

example : productConclusion Z0 Z0 Z0 (0) zero_split :=
  zero_split.exists_product_model_of_dimH_factor_le_one
    zsegments zcomparison zdimension (0)

example : productConclusion ℝ Z0 ℝ 0 zero_split := by
  have hc := polynomial_covering_of_growing_local_geometry (fun _ : ℕ => (0 : ℝ))
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
  exact (PointedGHConverges.const 0).exists_product_model_of_codimension_le_one
    (by omega : (0 : ℕ) ≤ 1) (by omega) hc real_segments
    (real_comparison (by norm_num)) zero_split

example : productConclusion ℝ Z0 ℝ 0 zero_split := by
  exact (PointedGHConverges.const 0).exists_product_model_of_growing_local_geometry
    (by omega : 1 ≤ (1 : ℕ)) (by omega) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le) zero_split

example : ∃ (Y : Type) (m : MetricSpace Y), letI := m
    ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℝ)) q ∧
      ∀ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∀ e : Y ≃ᵢ WithLp 2 (Z0 × Z), productConclusion Y Z0 Z q e := by
  obtain ⟨Y, m, q, φ, hφ, _, hproper, hconv, _, _, _, _, _⟩ :=
    exists_pointed_limit_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
      (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
      kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
  let := m
  let := hproper
  refine ⟨Y, m, q, φ, hφ, hconv, ?_⟩
  intro Z mZ e
  exact hconv.exists_product_model_of_growing_local_geometry
    (by omega : 1 ≤ (1 : ℕ)) (by omega) (fun _ => real_curves) (fun i => (kappas_pos (φ i)).le)
    (kappas_zero.comp hφ.tendsto_atTop) (radii_top.comp hφ.tendsto_atTop)
    (fun i => real_dim (φ i)) (fun i z _ => ambient_local z (kappas_pos (φ i)).le) e


example (p : C) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ T : Finset C,
      (T.card : ℝ) ≤ (2 + 4 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℕ) *
        Real.sinh (2 * R)) ^ (1 : ℕ) * ε ^ (-((1 : ℕ) : ℝ)) ∧
      (∀ x ∈ T, dist x p ≤ R) ∧
      ∀ x : C, dist x p ≤ R → ∃ y ∈ T, dist x y ≤ ε :=
  exists_polynomial_net_of_nonnegative_comparison
    (arbitrarily_short_curves_of_metric_segments csegments) ccomparison
    (by omega : 1 ≤ (1 : ℕ)) (by simpa only [Nat.cast_one] using cdimension) p hR hε hεone

example : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset Z0,
      (T.card : ℝ) ≤ C * ε ^ (-((1 : ℕ) : ℝ)) ∧
      (∀ x ∈ T, dist x 0 ≤ R) ∧
      ∀ x : Z0, dist x 0 ≤ R → ∃ y ∈ T, dist x y ≤ ε :=
  polynomial_nets_of_nonnegative_comparison
    (arbitrarily_short_curves_of_metric_segments zsegments) zcomparison
    (by omega : 1 ≤ (1 : ℕ)) (by simpa only [Nat.cast_one] using zdimension) 0

example : (0 : ℕ) ≤ 1 ∧ dimH (univ : Set C) ≤ ENNReal.ofReal (((1 : ℕ) - 0 : ℕ) : ℝ) :=
  zero_split.euclidean_factor_dimension_of_nonnegative_comparison (by omega)
    (arbitrarily_short_curves_of_metric_segments csegments) ccomparison (by simpa only [Nat.cast_one] using cdimension) 0

example : productConclusion C Z0 C ((1 : ℝ) : C) zero_split :=
  zero_split.exists_product_model_of_nonnegative_comparison (by omega : 1 ≤ (1 : ℕ))
    (by omega) csegments ccomparison (by simpa only [Nat.cast_one] using cdimension) ((1 : ℝ) : C)

private noncomputable def one_basis : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv
private noncomputable def one_split : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z0) :=
  one_basis.trans (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin 1)) Z0).symm
private theorem one_split_zero : one_split 0 = WithLp.toLp 2 (0, (0 : Z0)) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero
  · exact Subsingleton.elim _ _
example : ∃ F : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1), F 0 = 0 :=
  one_split.exists_pointed_euclidean_of_nonnegative_comparison (n := 1) (by omega) real_segments
    (real_comparison (by norm_num)) (by simp only [Real.dimH_univ, Nat.cast_one]; exact le_rfl)
    0 0 one_split_zero

private noncomputable def real_split : ℝ ≃ᵢ WithLp 2 (ℝ × Z0) :=
  (IsometryEquiv.withLpProdUnique 2 ℝ Z0).symm
example (p : ℝ) : productConclusion ℝ ℝ Z0 p real_split :=
  real_split.exists_product_model_of_real_splitting_dimH_le_two real_segments
    (real_comparison (by norm_num)) (by rw [Real.dimH_univ]; norm_num) p

example (p : ℝ) :
    (∃ F : ℝ ≃ᵢ ℝ, ∀ x, F x = lineCoordinate (fun t : ℝ => t) x) ∨
    (∃ F : ℝ ≃ᵢ WithLp 2 (ℝ × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = lineCoordinate (fun t : ℝ => t) x) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : ℝ ≃ᵢ WithLp 2 (ℝ × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = lineCoordinate (fun t : ℝ => t) x) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : ℝ ≃ᵢ WithLp 2 (ℝ × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = lineCoordinate (fun t : ℝ => t) x) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : ℝ ≃ᵢ WithLp 2 (ℝ × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = lineCoordinate (fun t : ℝ => t) x) :=
  exists_product_model_of_line_dimH_le_two real_segments (real_comparison (by norm_num))
    (by rw [Real.dimH_univ]; norm_num) isometry_id p

#print axioms exists_polynomial_net_of_nonnegative_comparison

#print axioms polynomial_nets_of_nonnegative_comparison

#print axioms IsometryEquiv.euclidean_factor_dimension_of_nonnegative_comparison

#print axioms IsometryEquiv.exists_pointed_euclidean_of_nonnegative_comparison

#print axioms IsometryEquiv.exists_product_model_of_nonnegative_comparison

#print axioms IsometryEquiv.exists_product_model_of_real_splitting_dimH_le_two

#print axioms exists_product_model_of_line_dimH_le_two
```
