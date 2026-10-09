import DifferentialGeometry.Geometry.Coordinates.StereographicDisk
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlane
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryNormalization
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMapMetric
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundarySimilarity
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTranslation

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "H3" => Hyperboloid E3
local notation "S2" => Metric.sphere (0 : E3) 1

private def planeAffine (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

private theorem planeAffine_apply (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    planeAffine a b ha z = a * z + b := rfl

private def boundaryAffine (a b : ℂ) (ha : a ≠ 0) : H3 ≃ᵢ H3 :=
  (boundarySimilarity a ha).trans (boundaryTranslation b)

private theorem boundaryAffine_north (a b : ℂ) (ha : a ≠ 0) :
    boundaryHomeomorph (boundaryAffine a b ha) sphereNorthPole = sphereNorthPole := by
  simp only [boundaryAffine, boundaryHomeomorph_trans, Homeomorph.trans_apply,
    boundaryHomeomorph_boundarySimilarity_northPole, boundaryHomeomorph_boundaryTranslation_northPole]

private theorem boundaryAffine_chart (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    boundaryHomeomorph (boundaryAffine a b ha) (stereographicComplex.symm z).val =
      (stereographicComplex.symm (planeAffine a b ha z)).val := by
  simp only [boundaryAffine, boundaryHomeomorph_trans, Homeomorph.trans_apply,
    boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm,
    boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm, planeAffine_apply]

private theorem isometry_distortion (e : H3 ≃ᵢ H3) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (e x) (e y) ∧ dist (e x) (e y) ≤ L * dist x y + C := by
  refine ⟨1, 0, le_rfl, le_rfl, ?_⟩
  intro x y
  simp only [e.dist_eq, inv_one, one_mul, sub_zero, add_zero, le_refl, and_self]

private theorem boundaryMap_isometry_conjugate
    (f : C(H3, H3)) (A B : H3 ≃ᵢ H3)
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hf0 : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (B.symm (f (A x))) (B.symm (f (A y))) ∧
        dist (B.symm (f (A x))) (B.symm (f (A y))) ≤ L * dist x y + C) (ξ : S2) :
    boundaryMap ((B.symm : C(H3, H3)).comp (f.comp (A : C(H3, H3)))) hf0 ξ =
      (boundaryHomeomorph B).symm (boundaryMap f hf (boundaryHomeomorph A ξ)) := by
  have hfA : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist ((f.comp (A : C(H3, H3))) x) ((f.comp (A : C(H3, H3))) y) ∧
        dist ((f.comp (A : C(H3, H3))) x) ((f.comp (A : C(H3, H3))) y) ≤ L * dist x y + C := by
    obtain ⟨L, C, hL, hC, hxy⟩ := hf
    refine ⟨L, C, hL, hC, fun x y => ?_⟩
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, A.dist_eq] using hxy (A x) (A y)
  rw [boundaryMap_comp (f.comp (A : C(H3, H3))) (B.symm : C(H3, H3)) hfA
    (isometry_distortion B.symm)]
  rw [boundaryMap_comp (A : C(H3, H3)) f (isometry_distortion A) hf]
  simp only [ContinuousMap.comp_apply, boundaryMap_isometryEquiv, ContinuousMap.coe_apply,
    boundaryHomeomorph_symm]

private def stereographicTriple : Fin 3 → S2 :=
  ![sphereNorthPole, (stereographicComplex.symm 0).val, (stereographicComplex.symm 1).val]

private theorem stereographicTriple_injective : Function.Injective stereographicTriple := by
  intro i j h
  have hz := (stereographicComplex.symm (0 : ℂ)).property
  have ho := (stereographicComplex.symm (1 : ℂ)).property
  have hzo : (stereographicComplex.symm (0 : ℂ)).val ≠
      (stereographicComplex.symm (1 : ℂ)).val := by
    intro he
    have he' := stereographicComplex.symm.injective (Subtype.ext he)
    exact zero_ne_one he'
  fin_cases i <;> fin_cases j <;> simp_all [stereographicTriple]

private theorem exists_normalized_plane_disk_inclusions (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 ≤ R ∧ ∀ (g : C(H3, H3))
      (hg : ∀ x y : H3, L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧
        dist (g x) (g y) ≤ L * dist x y + C) (Q : S2 ≃ₜ S2) (h : ℂ ≃ₜ ℂ),
      (∀ ξ : S2, boundaryMap g ⟨L, C, hL, hC, hg⟩ ξ = Q.symm ξ) →
      (∀ z : ℂ, (stereographicComplex.symm (h z)).val = Q (stereographicComplex.symm z).val) →
      h 0 = 0 → h 1 = 1 → Q sphereNorthPole = sphereNorthPole →
      Metric.closedBall (0 : ℂ) ρ ⊆ h '' Metric.ball 0 1 ∧
        h '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall 0 R := by
  obtain ⟨B, hB, hbound⟩ := exists_origin_displacement_bound_of_boundaryMap_fixed_triple
    L C hL hC stereographicTriple stereographicTriple_injective
  obtain ⟨H, hH, hholder⟩ := exists_boundaryMap_half_chord_bound (E := E3) (F := E3) L C B hL hC hB
  obtain ⟨ρ, R, hρ, hR, hdisk⟩ := exists_stereographic_disk_inclusions_of_inverse_holder
    H (1 / (2 * L)) hH (by positivity)
  refine ⟨ρ, R, hρ, hR, ?_⟩
  intro g hg Q h hginv hchart hzero hone hnorth
  have hfix (j : Fin 3) : Q (stereographicTriple j) = stereographicTriple j := by
    fin_cases j
    · exact hnorth
    · exact (hchart 0).symm.trans (congrArg (fun z : ℂ => (stereographicComplex.symm z).val) hzero)
    · exact (hchart 1).symm.trans (congrArg (fun z : ℂ => (stereographicComplex.symm z).val) hone)
  have hgbound : dist (origin : H3) (g origin) ≤ B := by
    apply hbound g hg
    intro j
    rw [hginv]
    exact (congrArg Q.symm (hfix j).symm).trans (Q.symm_apply_apply _)
  apply hdisk Q h hchart hzero hnorth
  intro ξ η
  rw [← hginv ξ, ← hginv η]
  exact hholder g hg hgbound ξ η

private theorem planeAffine_dist (a b : ℂ) (ha : a ≠ 0) (w : ℂ) :
    dist (planeAffine a b ha w) b = ‖a‖ * ‖w‖ := by
  rw [dist_eq_norm, planeAffine_apply, add_sub_cancel_right, norm_mul]

private theorem plane_disk_inclusions_of_normalization
    (h : ℂ ≃ₜ ℂ) (z a : ℂ) (ha : a ≠ 0) (r : ℝ) (hr : 0 < r)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hin : Metric.closedBall (0 : ℂ) ρ ⊆
      ((planeAffine (r : ℂ) z (Complex.ofReal_ne_zero.mpr hr.ne')).trans
        (h.trans (planeAffine a (h z) ha).symm)) '' Metric.ball 0 1)
    (hout : ((planeAffine (r : ℂ) z (Complex.ofReal_ne_zero.mpr hr.ne')).trans
        (h.trans (planeAffine a (h z) ha).symm)) '' Metric.closedBall (0 : ℂ) 1 ⊆
      Metric.closedBall 0 R) :
    0 < ‖a‖ * ρ ∧ 0 ≤ ‖a‖ * R ∧
      Metric.closedBall (h z) (‖a‖ * ρ) ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) (‖a‖ * R) := by
  let α := planeAffine (r : ℂ) z (Complex.ofReal_ne_zero.mpr hr.ne')
  let β := planeAffine a (h z) ha
  let h0 := α.trans (h.trans β.symm)
  have hβ (w : ℂ) : β (h0 w) = h (α w) := β.apply_symm_apply _
  have hαdist (w : ℂ) : dist (α w) z = r * ‖w‖ := by
    rw [planeAffine_dist, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hβdist (w : ℂ) : dist (β w) (h z) = ‖a‖ * ‖w‖ := planeAffine_dist a (h z) ha w
  have haNorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨mul_pos haNorm hρ, mul_nonneg haNorm.le hR, ?_, ?_⟩
  · intro w hw
    have hw' : ‖β.symm w‖ ≤ ρ := by
      apply (mul_le_mul_iff_right₀ haNorm).mp
      rw [← hβdist, β.apply_symm_apply]
      exact hw
    obtain ⟨u, hu, he⟩ := hin (show β.symm w ∈ Metric.closedBall (0 : ℂ) ρ by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw')
    refine ⟨α u, ?_, ?_⟩
    · rw [Metric.mem_ball, hαdist]
      have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
      simpa only [mul_one] using mul_lt_mul_of_pos_left hu' hr
    · exact (hβ u).symm.trans ((congrArg β he).trans (β.apply_symm_apply w))
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : ‖α.symm w‖ ≤ 1 := by
      apply (mul_le_mul_iff_right₀ hr).mp
      rw [mul_one, ← hαdist, α.apply_symm_apply]
      exact hw
    have ho := hout ⟨α.symm w,
      show α.symm w ∈ Metric.closedBall (0 : ℂ) 1 by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hw', rfl⟩
    have ho' : ‖h0 (α.symm w)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using ho
    rw [Metric.mem_closedBall, ← α.apply_symm_apply w, ← hβ, hβdist]
    exact mul_le_mul_of_nonneg_left ho' haNorm.le

theorem exists_boundaryPlaneHomeomorph_disk_inclusions
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∀ (f g : C(H3, H3))
      (hf : ∀ x y : H3, L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ L * dist x y + C)
      (hg : ∀ x y : H3, L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧
        dist (g x) (g y) ≤ L * dist x y + C)
      (hgf : ∃ D : ℝ, ∀ x : H3, dist (g (f x)) x ≤ D)
      (hfg : ∃ D : ℝ, ∀ x : H3, dist (f (g x)) x ≤ D)
      (hnorth : boundaryMap f ⟨L, C, hL, hC, hf⟩ sphereNorthPole = sphereNorthPole),
      let h := boundaryPlaneHomeomorph f g ⟨L, C, hL, hC, hf⟩ ⟨L, C, hL, hC, hg⟩ hgf hfg hnorth
      ∀ (z : ℂ) (r : ℝ), 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧ 0 ≤ R ∧
        Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
        h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ := by
  obtain ⟨ρ, R, hρ, hR, hnormalized⟩ := exists_normalized_plane_disk_inclusions L C hL hC
  refine ⟨max 1 (R / ρ), le_max_left _ _, ?_⟩
  intro f g hf hg hgf hfg hnorth h z r hr
  let Q := boundaryHomeomorphOfCoarseInverse f g ⟨L, C, hL, hC, hf⟩
    ⟨L, C, hL, hC, hg⟩ hgf hfg
  have hchart (w : ℂ) : (stereographicComplex.symm (h w)).val = Q (stereographicComplex.symm w).val :=
    stereographicComplex_symm_boundaryPlaneHomeomorph f g ⟨L, C, hL, hC, hf⟩
      ⟨L, C, hL, hC, hg⟩ hgf hfg hnorth w
  let a := h (z + (r : ℂ)) - h z
  have ha : a ≠ 0 := by
    intro he
    have hz : z + (r : ℂ) = z := h.injective (sub_eq_zero.mp he)
    have hz' : (r : ℂ) = 0 := add_left_cancel (hz.trans (add_zero z).symm)
    exact hr.ne' (Complex.ofReal_eq_zero.mp hz')
  let α := planeAffine (r : ℂ) z (Complex.ofReal_ne_zero.mpr hr.ne')
  let β := planeAffine a (h z) ha
  let A := boundaryAffine (r : ℂ) z (Complex.ofReal_ne_zero.mpr hr.ne')
  let B := boundaryAffine a (h z) ha
  let h0 := α.trans (h.trans β.symm)
  let Q0 := (boundaryHomeomorph A).trans (Q.trans (boundaryHomeomorph B).symm)
  let g0 : C(H3, H3) := (A.symm : C(H3, H3)).comp (g.comp (B : C(H3, H3)))
  have hg0 (x y : H3) : L⁻¹ * dist x y - C ≤ dist (g0 x) (g0 y) ∧
      dist (g0 x) (g0 y) ≤ L * dist x y + C := by
    have hb := hg (B x) (B y)
    simpa only [g0, ContinuousMap.comp_apply, ContinuousMap.coe_apply, A.symm.dist_eq,
      B.dist_eq] using hb
  have hg0boundary (ξ : S2) : boundaryMap g0 ⟨L, C, hL, hC, hg0⟩ ξ = Q0.symm ξ :=
    boundaryMap_isometry_conjugate g B A ⟨L, C, hL, hC, hg⟩ ⟨L, C, hL, hC, hg0⟩ ξ
  have hβ (w : ℂ) : β (h0 w) = h (α w) := β.apply_symm_apply _
  have h0chart (w : ℂ) : (stereographicComplex.symm (h0 w)).val =
      Q0 (stereographicComplex.symm w).val := by
    apply (boundaryHomeomorph B).injective
    change boundaryHomeomorph B (stereographicComplex.symm (h0 w)).val =
      boundaryHomeomorph B ((boundaryHomeomorph B).symm
        (Q (boundaryHomeomorph A (stereographicComplex.symm w).val)))
    rw [(boundaryHomeomorph B).apply_symm_apply]
    rw [boundaryAffine_chart, boundaryAffine_chart, hβ, hchart]
  have h0zero : h0 0 = 0 := by
    apply β.injective
    rw [hβ]
    simp only [α, β, planeAffine_apply, mul_zero, zero_add]
  have h0one : h0 1 = 1 := by
    apply β.injective
    rw [hβ]
    simp only [α, β, planeAffine_apply, mul_one]
    change h ((r : ℂ) + z) = h (z + (r : ℂ)) - h z + h z
    rw [add_comm (r : ℂ) z, sub_add_cancel]
  have h0north : Q0 sphereNorthPole = sphereNorthPole := by
    change (boundaryHomeomorph B).symm (Q (boundaryHomeomorph A sphereNorthPole)) = sphereNorthPole
    rw [boundaryAffine_north]
    change (boundaryHomeomorph B).symm (boundaryMap f ⟨L, C, hL, hC, hf⟩ sphereNorthPole) = sphereNorthPole
    rw [hnorth]
    exact (congrArg (boundaryHomeomorph B).symm (boundaryAffine_north a (h z) ha).symm).trans
      ((boundaryHomeomorph B).symm_apply_apply _)
  obtain ⟨hin, hout⟩ := hnormalized g0 hg0 Q0 h0 hg0boundary h0chart h0zero h0one h0north
  obtain ⟨hρ', hR', hin', hout'⟩ := plane_disk_inclusions_of_normalization h z a ha r hr ρ R hρ hR hin hout
  refine ⟨‖a‖ * ρ, ‖a‖ * R, hρ', hR', hin', hout', ?_⟩
  have hratio : R ≤ max 1 (R / ρ) * ρ :=
    (div_le_iff₀ hρ).mp (le_max_right _ _)
  have hm := mul_le_mul_of_nonneg_left hratio (norm_nonneg a)
  calc
    ‖a‖ * R ≤ ‖a‖ * (max 1 (R / ρ) * ρ) := hm
    _ = max 1 (R / ρ) * (‖a‖ * ρ) := by ring

end DifferentialGeometry.Hyperboloid
