import DifferentialGeometry.Topology.Homeomorph.Graph
import DifferentialGeometry.Topology.Embedding.CylinderCapRounding

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem cylinder_cap_coordinates_mem_cylinder
    {a δ R b : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hR : 1 < R)
    (hδb : δ < b - a) (hδR : 2 * δ / a < R ^ 2 - 1)
    {x : E} (hx : x ∈ closedBall 0 1) {t : ℝ} (ht : t ∈ Icc (-δ) (a + δ)) :
    Diffeomorph.cylinderCapCoordinates a (x, t) ∈ ball (0 : E) R ×ˢ Ioo (-b) b := by
  have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hxsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  let z := t + a * (‖x‖ ^ 2 - 1)
  let M := Real.smoothMax (1 / 4) (1 / 2) (1 + z / a)
  have hMhalf : 1 / 2 ≤ M :=
    (le_max_left _ _).trans (Real.smoothMax.max_le (by norm_num) _ _)
  have hM : 0 < M := by linarith
  have hz : 1 + z / a = ‖x‖ ^ 2 + t / a := by
    dsimp [z]
    field_simp
    ring
  have harg : 1 + z / a ≤ M :=
    (le_max_right _ _).trans (Real.smoothMax.max_le (by norm_num) _ _)
  have htdiv : -δ / a ≤ t / a := div_le_div_of_nonneg_right ht.1 ha.le
  have hsM : ‖x‖ ^ 2 ≤ M + δ / a := by
    rw [hz] at harg
    rw [neg_div] at htdiv
    linarith
  have hprod := mul_le_mul_of_nonneg_right hMhalf (div_nonneg hδ.le ha.le)
  have hsratio : ‖x‖ ^ 2 ≤ M * (1 + 2 * δ / a) := by
    have heq : M * (1 + 2 * δ / a) = M + 2 * (M * (δ / a)) := by ring
    rw [heq]
    linarith
  have hsR : ‖x‖ ^ 2 < M * R ^ 2 := hsratio.trans_lt
    (mul_lt_mul_of_pos_left (by linarith : 1 + 2 * δ / a < R ^ 2) hM)
  have hnormsq : ‖(Real.sqrt M)⁻¹ • x‖ ^ 2 < R ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hM),
      mul_pow, inv_pow, Real.sq_sqrt hM.le, inv_mul_eq_div]
    exact (div_lt_iff₀ hM).mpr (by nlinarith [hsR])
  have hzl : -b < z := by
    have := mul_nonneg ha.le (sq_nonneg ‖x‖)
    dsimp [z]
    nlinarith [ht.1]
  have hzu : z < b := by
    have := mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hxsq)
    dsimp [z]
    linarith [ht.2]
  rw [Diffeomorph.cylinderCapCoordinates_apply]
  refine ⟨?_, hzl, hzu⟩
  rw [mem_ball_zero_iff]
  change ‖(Real.sqrt M)⁻¹ • x‖ < R
  nlinarith [norm_nonneg ((Real.sqrt M)⁻¹ • x)]

theorem exists_cylinderCap_flattening_of_pos [ProperSpace E]
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 1 < R) :
    ∃ H : (E × ℝ) ≃ₜ (E × ℝ),
      (∀ x ∈ closedBall (0 : E) 1, H (EuclideanGeometry.cylinderCap a x) = (x, 0)) ∧
      (∀ p : E × ℝ, ‖p.1‖ = 1 → 0 ≤ p.2 → H p = p) ∧
      ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ ball (0 : E) R ×ˢ Ioo (-b) b ∧
        EqOn H id Cᶜ ∧ EqOn H.symm id Cᶜ := by
  have hRpos : 0 < R ^ 2 - 1 := by nlinarith
  obtain ⟨δ, hδ, hδmin⟩ := exists_between
    (lt_min (sub_pos.mpr hab) (div_pos (mul_pos ha hRpos) (by norm_num : (0 : ℝ) < 2)))
  have hδb : δ < b - a := hδmin.trans_le (min_le_left _ _)
  have hδR : 2 * δ / a < R ^ 2 - 1 := by
    apply (div_lt_iff₀ ha).mpr
    have hh := hδmin.trans_le (min_le_right _ _)
    nlinarith
  let f : E → ℝ := fun x => a * max 0 (1 - ‖x‖ ^ 2)
  have hf : Continuous f := continuous_const.mul
    (continuous_const.max (continuous_const.sub (continuous_norm.pow 2)))
  have hf_bounds (x : E) : 0 ≤ f x ∧ f x ≤ a := by
    refine ⟨mul_nonneg ha.le (le_max_left _ _), ?_⟩
    have hh : max 0 (1 - ‖x‖ ^ 2) ≤ 1 := max_le (by norm_num) (by nlinarith [sq_nonneg ‖x‖])
    exact (mul_le_mul_of_nonneg_left hh ha.le).trans_eq (mul_one a)
  have hzero {x : E} (hx : 1 ≤ ‖x‖ ^ 2) : f x = 0 := by
    simp only [f, max_eq_left (sub_nonpos.mpr hx), mul_zero]
  have hf_support : tsupport f ⊆ closedBall (0 : E) 1 := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hxnorm : 1 < ‖x‖ := lt_of_not_ge (fun hh => hn (mem_closedBall_zero_iff.mpr hh))
    exact hx (hzero (by nlinarith))
  have hbound (x : E) : f x ∈ Ioo (-δ) (a + δ) := by
    obtain ⟨h₀, h₁⟩ := hf_bounds x
    constructor <;> linarith
  let G := graphShift hf (neg_lt_zero.mpr hδ) (by linarith : 0 < a + δ) hbound
  let D := (Diffeomorph.cylinderCapCoordinates (E := E) a).toHomeomorph
  let H := D.symm.trans (G.trans D)
  let B := closedBall (0 : E) 1 ×ˢ Icc (-δ) (a + δ)
  have hGfix : EqOn G id Bᶜ := by
    intro p hp
    apply graphShift_eqOn_compl hf (neg_lt_zero.mpr hδ) (by linarith) hbound
    exact fun hh => hp ⟨hf_support hh.1, hh.2⟩
  have hGsymfix : EqOn G.symm id Bᶜ := by
    intro p hp
    calc
      G.symm p = G.symm (G p) := congrArg G.symm (hGfix hp).symm
      _ = p := G.symm_apply_apply p
  refine ⟨H, ?_, ?_, D '' B,
    ((isCompact_closedBall (0 : E) 1).prod isCompact_Icc).image D.continuous, ?_, ?_, ?_⟩
  · intro x hx
    have hxsq : ‖x‖ ^ 2 ≤ 1 := by
      have hn := mem_closedBall_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    have hinv : D.symm (x, 0) = (x, f x) := by
      rw [show D.symm (x, 0) =
        (Diffeomorph.cylinderCapCoordinates a).symm (x, 0) from rfl,
        Diffeomorph.cylinderCapCoordinates_symm_apply_of_snd_nonneg ha (le_refl 0)]
      simp only [zero_div, add_zero, Real.sqrt_one, one_smul, f,
        max_eq_right (sub_nonneg.mpr hxsq)]
    change D (G (D.symm (EuclideanGeometry.cylinderCap a x))) = (x, 0)
    rw [← Diffeomorph.cylinderCapCoordinates_apply_zero ha.ne' x]
    change D (G (D.symm (D (x, 0)))) = (x, 0)
    rw [D.symm_apply_apply, graphShift_apply_zero, ← hinv, D.apply_symm_apply]
  · intro p hp ht
    have hnorm : ‖(D.symm p).1‖ ^ 2 = 1 + p.2 / a := by
      rw [show D.symm p = (Diffeomorph.cylinderCapCoordinates a).symm p from rfl,
        Diffeomorph.cylinderCapCoordinates_symm_apply_of_snd_nonneg ha ht]
      change ‖Real.sqrt (1 + p.2 / a) • p.1‖ ^ 2 = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hp, mul_one,
        Real.sq_sqrt (by have := div_nonneg ht ha.le; linarith)]
    have hfz : f (D.symm p).1 = 0 := hzero (by rw [hnorm]; have := div_nonneg ht ha.le; linarith)
    change D (G (D.symm p)) = p
    rw [graphShift_eq_self_of_eq_zero hf (neg_lt_zero.mpr hδ) (by linarith) hbound hfz,
      D.apply_symm_apply]
  · rintro p ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact cylinder_cap_coordinates_mem_cylinder ha hδ hR hδb hδR hx ht
  · intro p hp
    have hq : D.symm p ∉ B := fun hq => hp ⟨D.symm p, hq, D.apply_symm_apply p⟩
    change D (G (D.symm p)) = p
    rw [hGfix hq, id_eq, D.apply_symm_apply]
  · intro p hp
    have hq : D.symm p ∉ B := fun hq => hp ⟨D.symm p, hq, D.apply_symm_apply p⟩
    change D (G.symm (D.symm p)) = p
    rw [hGsymfix hq, id_eq, D.apply_symm_apply]

theorem exists_cylinderCap_flattening [ProperSpace E]
    {a b R : ℝ} (ha : a ≠ 0) (hab : |a| < b) (hR : 1 < R) :
    ∃ H : (E × ℝ) ≃ₜ (E × ℝ),
      (∀ x ∈ closedBall (0 : E) 1, H (EuclideanGeometry.cylinderCap a x) = (x, 0)) ∧
      (∀ p : E × ℝ, ‖p.1‖ = 1 → 0 ≤ a * p.2 → H p = p) ∧
      ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ ball (0 : E) R ×ˢ Ioo (-b) b ∧
        EqOn H id Cᶜ ∧ EqOn H.symm id Cᶜ := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · obtain ⟨H, hcap, hwall, C, hC, hCU, hfix, hifix⟩ :=
      exists_cylinderCap_flattening_of_pos (E := E) (neg_pos.mpr ha)
        (by simpa only [abs_of_neg ha] using hab) hR
    let S : (E × ℝ) ≃ₜ (E × ℝ) := (Homeomorph.refl E).prodCongr (Homeomorph.neg ℝ)
    have hSS (p : E × ℝ) : S (S p) = p := Prod.ext rfl (neg_neg p.2)
    have hScap (x : E) : S (EuclideanGeometry.cylinderCap a x) =
        EuclideanGeometry.cylinderCap (-a) x := by
      rw [EuclideanGeometry.cylinderCap_neg]
      rfl
    refine ⟨S.trans (H.trans S), ?_, ?_, S '' C, hC.image S.continuous, ?_, ?_, ?_⟩
    · intro x hx
      change S (H (S (EuclideanGeometry.cylinderCap a x))) = (x, 0)
      rw [hScap, hcap x hx]
      exact Prod.ext rfl neg_zero
    · intro p hp ht
      change S (H (S p)) = p
      rw [hwall (S p) hp (neg_nonneg.mpr (nonpos_of_mul_nonneg_right ht ha)), hSS]
    · rintro p ⟨q, hq, rfl⟩
      have hqU := hCU hq
      refine ⟨hqU.1, ?_, ?_⟩
      · change -b < -q.2
        linarith [hqU.2.2]
      · change -q.2 < b
        linarith [hqU.2.1]
    · intro p hp
      have hq : S p ∉ C := fun hq => hp ⟨S p, hq, hSS p⟩
      change S (H (S p)) = p
      rw [hfix hq, id_eq, hSS]
    · intro p hp
      have hq : S p ∉ C := fun hq => hp ⟨S p, hq, hSS p⟩
      change S (H.symm (S p)) = p
      rw [hifix hq, id_eq, hSS]
  · obtain ⟨H, hcap, hwall, C, hC, hCU, hfix, hifix⟩ :=
      exists_cylinderCap_flattening_of_pos (E := E) ha
        (by simpa only [abs_of_pos ha] using hab) hR
    exact ⟨H, hcap, fun p hp ht => hwall p hp (nonneg_of_mul_nonneg_right ht ha),
      C, hC, hCU, hfix, hifix⟩

end Homeomorph
