import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Interior

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

variable (P : S3)

theorem stereographicSmallBallChart_image_closedBall_one :
    (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 =
      (stereographic' 3 P).symm '' Metric.closedBall 0 (1 / 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-(1 / 2 : ℝ)) • x, ?_, (stereographicSmallBallChart_apply P x).symm⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    norm_num
    linarith
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-2 : ℝ) • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      have hx' : ‖x‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      norm_num
      linarith
    · rw [stereographicSmallBallChart_apply, smul_smul]
      norm_num

private theorem cylinder_radius_norm (p : S2 × Icc (0 : ℝ) 1) :
    ‖((1 / 2 : ℝ) + (8 - 1 / 2) * p.2.val) • (-p.1).val‖ =
      1 / 2 + (8 - 1 / 2) * p.2.val := by
  rw [norm_smul, Real.norm_of_nonneg (by nlinarith [p.2.property.1]), norm_eq_of_mem_sphere, mul_one]

theorem sphereDoublePuncturedHomeomorph_mem_first_closedBall (p : S2 × Icc (0 : ℝ) 1) :
    (sphereDoublePuncturedHomeomorph P p).val ∈
      (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ↔ p.2.val = 0 := by
  rw [stereographicSmallBallChart_image_closedBall_one, sphereDoublePuncturedHomeomorph_apply]
  rw [((stereographic' 3 P).symm.isOpenEmbedding (by simp)).injective.mem_set_image,
    Metric.mem_closedBall, dist_zero_right, cylinder_radius_norm]
  constructor <;> intro h <;> nlinarith [p.2.property.1]

theorem sphereDoublePuncturedHomeomorph_mem_second_closedBall (p : S2 × Icc (0 : ℝ) 1) :
    (sphereDoublePuncturedHomeomorph P p).val ∈
      (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ↔ p.2.val = 1 := by
  rw [oppositeStereographicSmallBallChart_image, stereographicSmallBallChart_image_closedBall_one,
    sphereDoublePuncturedHomeomorph_apply]
  have hneg (x : S3) : x ∈ Neg.neg '' ((stereographic' 3 P).symm '' Metric.closedBall 0 (1 / 2)) ↔
      -x ∈ (stereographic' 3 P).symm '' Metric.closedBall 0 (1 / 2) := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [neg_neg] using hy
    · intro h
      exact ⟨-x, h, neg_neg x⟩
  rw [hneg]
  have h := mem_antipodal_stereographic_symm_closedBall (n := 3) P (by norm_num : (0 : ℝ) < 8)
    (((1 / 2 : ℝ) + (8 - 1 / 2) * p.2.val) • (-p.1).val)
  rw [show (4 : ℝ) / 8 = 1 / 2 by norm_num, cylinder_radius_norm] at h
  rw [h]
  constructor <;> intro h' <;> nlinarith [p.2.property.2]

variable (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
  (h0 : D 0 = 0) (h1 : D 1 = 1)

include h0 h1 in
theorem sphereDoublePuncturedInteriorImage_eq :
    (sphereDoublePuncturedInteriorImage P D hI : Set S3) =
      ((stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
        (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1)ᶜ := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩ (hc | hd)
    · have he := (sphereDoublePuncturedHomeomorph_mem_first_closedBall P _).mp hc
      change D p.val.2 = 0 at he
      have hp0 := D.injective (he.trans h0.symm)
      exact p.property.2.1.ne' hp0
    · have he := (sphereDoublePuncturedHomeomorph_mem_second_closedBall P _).mp hd
      change D p.val.2 = 1 at he
      have hp1 := D.injective (he.trans h1.symm)
      exact p.property.2.2.ne hp1
  · intro hx
    have hxK : x ∈ ((stereographicSmallBallChart P).chart '' Metric.ball 0 1 ∪
        (oppositeStereographicSmallBallChart P).chart '' Metric.ball 0 1)ᶜ := by
      rintro (hc | hd)
      · exact hx (Or.inl (Set.image_mono Metric.ball_subset_closedBall hc))
      · exact hx (Or.inr (Set.image_mono Metric.ball_subset_closedBall hd))
    let p := (sphereDoublePuncturedHomeomorph P).symm ⟨x, hxK⟩
    have hp : (sphereDoublePuncturedHomeomorph P p).val = x :=
      congrArg Subtype.val ((sphereDoublePuncturedHomeomorph P).apply_symm_apply ⟨x, hxK⟩)
    let t := (unitIntervalRestriction D hI).symm p.2
    have ht : (unitIntervalRestriction D hI t).val = p.2.val :=
      congrArg Subtype.val ((unitIntervalRestriction D hI).apply_symm_apply p.2)
    have ht0 : t.val ≠ 0 := by
      intro he
      have he0 : p.2.val = 0 := ht.symm.trans (by rw [unitIntervalRestriction_apply, he, h0])
      exact hx (Or.inl (hp ▸ (sphereDoublePuncturedHomeomorph_mem_first_closedBall P p).mpr he0))
    have ht1 : t.val ≠ 1 := by
      intro he
      have he1 : p.2.val = 1 := ht.symm.trans (by rw [unitIntervalRestriction_apply, he, h1])
      exact hx (Or.inr (hp ▸ (sphereDoublePuncturedHomeomorph_mem_second_closedBall P p).mpr he1))
    let q : DoubleCylinder.Interior := ⟨(p.1, t.val), mem_univ _,
      lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
    refine ⟨q, ?_⟩
    change (sphereDoublePuncturedHomeomorph P (p.1, unitIntervalRestriction D hI t)).val = x
    rw [(unitIntervalRestriction D hI).apply_symm_apply]
    exact hp

end DifferentialGeometry.Topology.Manifold
