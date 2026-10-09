import DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import DifferentialGeometry.Topology.Manifold.StereographicCylinder
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereUnitFilling
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

theorem stereographic_double_cap_complement (P : S3) {a b : ℝ} (hb : 0 < b) :
    (((stereographic' 3 P).symm '' Metric.ball 0 a) ∪
      Neg.neg '' ((stereographic' 3 P).symm '' Metric.ball 0 (4 / b)))ᶜ =
        (stereographic' 3 P).symm '' (Metric.closedBall 0 b \ Metric.ball 0 a) := by
  let e := (stereographic' 3 P).symm
  have hinj : Injective e := e.isOpenEmbedding (by simp [e]) |>.injective
  have houter := antipodal_image_stereographic_symm_closedBall (n := 3) P (by positivity : 0 < 4 / b)
  have hcancel : 4 / (4 / b) = b := by field_simp
  rw [hcancel] at houter
  have hout (x : S3) : x ∉ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔
      x ∈ e '' Metric.closedBall 0 b := by
    have hneg : x ∈ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔
        -x ∈ e '' Metric.ball 0 (4 / b) := by
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [neg_neg] using hy
      · intro hx
        exact ⟨-x, hx, neg_neg x⟩
    rw [hneg]
    change -x ∈ (e '' Metric.ball 0 (4 / b))ᶜ ↔ _
    rw [← houter]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : y = x := neg_injective heq
      exact hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext x
  change x ∉ e '' Metric.ball 0 a ∪ Neg.neg '' (e '' Metric.ball 0 (4 / b)) ↔ _
  rw [mem_union, not_or, hout]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨y, ⟨hy, fun hya => hx ⟨y, hya, rfl⟩⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hya⟩, rfl⟩
    refine ⟨?_, ⟨y, hy, rfl⟩⟩
    rintro ⟨z, hz, heq⟩
    exact hya (hinj heq ▸ hz)

def closedStereographicCylinderMap (P : S3) (a b : ℝ)
    (p : S2 × Icc (0 : ℝ) 1) : S3 :=
  (stereographic' 3 P).symm ((a + (b - a) * p.2.val) • p.1.val)

theorem continuous_closedStereographicCylinderMap (P : S3) (a b : ℝ) :
    Continuous (closedStereographicCylinderMap P a b) :=
  ((stereographic' 3 P).symm.isOpenEmbedding (by simp)).continuous.comp
    ((continuous_const.add (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).smul
      (continuous_subtype_val.comp continuous_fst))

theorem closedStereographicCylinderMap_injective (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) : Injective (closedStereographicCylinderMap P a b) := by
  intro p q h
  have heq := ((stereographic' 3 P).symm.isOpenEmbedding (by simp)).injective h
  have hp : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
  have hq : 0 < a + (b - a) * q.2.val := by nlinarith [q.2.property.1]
  have hn := congrArg norm heq
  simp only [norm_smul, Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hq.le,
    norm_eq_of_mem_sphere, mul_one] at hn
  have ht : p.2.val = q.2.val := by nlinarith
  apply Prod.ext _ (Subtype.ext ht)
  apply Subtype.ext
  change (a + (b - a) * p.2.val) • p.1.val = (a + (b - a) * q.2.val) • q.1.val at heq
  rw [ht] at heq
  exact smul_right_injective E3 hq.ne' heq

theorem range_closedStereographicCylinderMap (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    range (closedStereographicCylinderMap P a b) =
      (stereographic' 3 P).symm '' (Metric.closedBall 0 b \ Metric.ball 0 a) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have hr : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
    refine ⟨(a + (b - a) * p.2.val) • p.1.val, ⟨?_, ?_⟩, rfl⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le,
        norm_eq_of_mem_sphere, mul_one]
      nlinarith [p.2.property.2]
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le,
        norm_eq_of_mem_sphere, mul_one]
      nlinarith [p.2.property.1]
  · rintro ⟨y, ⟨hyb, hya⟩, rfl⟩
    have hya' : a ≤ ‖y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hya
    have hyb' : ‖y‖ ≤ b := by simpa only [Metric.mem_closedBall, dist_zero_right] using hyb
    have hypos : 0 < ‖y‖ := ha.trans_le hya'
    let z : S2 := ⟨‖y‖⁻¹ • y, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
        inv_mul_cancel₀ hypos.ne']⟩
    let t : Icc (0 : ℝ) 1 := ⟨(‖y‖ - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hya') (sub_pos.mpr hab).le,
      (div_le_iff₀ (sub_pos.mpr hab)).mpr (by linarith)⟩
    refine ⟨(z, t), ?_⟩
    change (stereographic' 3 P).symm
      ((a + (b - a) * ((‖y‖ - a) / (b - a))) • (‖y‖⁻¹ • y)) = _
    have hr : a + (b - a) * ((‖y‖ - a) / (b - a)) = ‖y‖ := by
      rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
      ring
    rw [hr, smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]

def closedStereographicCylinderHomeomorph (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    S2 × Icc (0 : ℝ) 1 ≃ₜ
      ↥((((stereographic' 3 P).symm '' Metric.ball 0 a) ∪
        Neg.neg '' ((stereographic' 3 P).symm '' Metric.ball 0 (4 / b)))ᶜ : Set S3) := by
  have hrange := (range_closedStereographicCylinderMap P ha hab).trans
    (stereographic_double_cap_complement P (ha.trans hab)).symm
  let F := closedStereographicCylinderMap P a b
  let H : S2 × Icc (0 : ℝ) 1 ≃ₜ range F :=
    (continuous_closedStereographicCylinderMap P a b).isClosedEmbedding
      (closedStereographicCylinderMap_injective P ha hab) |>.isEmbedding.toHomeomorph
  exact H.trans (Homeomorph.setCongr hrange)


private def affinePolarDiffeomorph (a b : ℝ) (hab : a < b) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (S2 × ℝ) (S2 × ℝ) ∞ where
  toFun p := (-p.1, (a + (b - a) * p.2) / 2)
  invFun p := (-p.1, (2 * p.2 - a) / (b - a))
  left_inv p := by
    refine Prod.ext (neg_neg p.1) ?_
    dsimp only
    field_simp [(sub_pos.mpr hab).ne']
    ring
  right_inv p := by
    refine Prod.ext (neg_neg p.1) ?_
    dsimp only
    rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
    ring
  contMDiff_toFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      ((contMDiff_const.add (contMDiff_const.mul contMDiff_snd)).div_const 2)
  contMDiff_invFun :=
    ((sphereAntipodalDiffeomorph (E := E3) (n := 2)).contMDiff.comp contMDiff_fst).prodMk
      ((contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const).div_const (b - a))

private def stereographicRadialPartial (P : S3) (a b : ℝ) (hab : a < b) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (S2 × ℝ) S3 ∞ :=
  ((affinePolarDiffeomorph a b hab).toPartialDiffeomorph.trans
    (DifferentialGeometry.Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2))).trans
      (SphereUnitFilling.sphereChartPartial P)

private theorem stereographicRadialPartial_apply (P : S3) (a b : ℝ) (hab : a < b)
    (p : S2 × ℝ) :
    stereographicRadialPartial P a b hab p =
      (stereographic' 3 P).symm ((a + (b - a) * p.2) • p.1.val) := by
  change (stereographic' 3 P).symm
    (-((2 : ℝ) • (((a + (b - a) * p.2) / 2) • (-p.1).val))) = _
  congr 1
  change -(2 • (((a + (b - a) * p.2) / 2) • -p.1.val)) = _
  module

theorem stereographic_radial_isLocalDiffeomorphAt (P : S3) (a b : ℝ) (hab : a < b)
    (p : S2 × ℝ) (hp : 0 < a + (b - a) * p.2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q : S2 × ℝ => (stereographic' 3 P).symm ((a + (b - a) * q.2) • q.1.val)) p := by
  refine ⟨stereographicRadialPartial P a b hab, ?_, ?_⟩
  · change (p ∈ univ ∧ 0 < (a + (b - a) * p.2) / 2) ∧ _ ∈ univ
    exact ⟨⟨mem_univ _, by positivity⟩, mem_univ _⟩
  · intro q _
    exact (stereographicRadialPartial_apply P a b hab q).symm

theorem contMDiff_closedStereographicCylinderMap (P : S3) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (closedStereographicCylinderMap P a b) := by
  intro p
  have hr : 0 < a + (b - a) * p.2.val := by nlinarith [p.2.property.1]
  have h := (stereographic_radial_isLocalDiffeomorphAt P a b hab (p.1, p.2.val) hr).contMDiffAt
  have hp : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : S2 × Icc (0 : ℝ) 1 => (q.1, q.2.val)) :=
    contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  have hcomp := h.comp p (hp.contMDiffAt (x := p))
  exact hcomp

theorem closedStereographicCylinderMap_lower (P : S3) (a b : ℝ) (z : S2) :
    closedStereographicCylinderMap P a b (z, ⟨0, by norm_num⟩) =
      (stereographic' 3 P).symm (a • z.val) := by
  simp [closedStereographicCylinderMap]

theorem closedStereographicCylinderMap_upper (P : S3) (a b : ℝ) (z : S2) :
    closedStereographicCylinderMap P a b (z, ⟨1, by norm_num⟩) =
      (stereographic' 3 P).symm (b • z.val) := by
  simp [closedStereographicCylinderMap]

end DifferentialGeometry.Topology.Manifold
