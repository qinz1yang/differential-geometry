import DifferentialGeometry.Geometry.Metric.CloudCrossTests

/-!
Two coordinate normal projections cannot approximate the same arbitrary real linear operator.
The actual cross cloud puts every sufficiently close coverage witness in both full-radius balls.
An isometric orthonormal coordinate change verifies the same obstruction in the ordinary
Euclidean real plane, and preserves the cloud rather than changing its norm.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry.CloudCounterexample

theorem horizontalNormal_one : horizontalNormal 1 = 0 := by
  apply Submodule.starProjection_orthogonal_apply_eq_zero
  exact (mem_horizontalLine (z := (1 : ℂ))).mpr (by simp)

theorem verticalNormal_one : verticalNormal 1 = 1 := by
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [verticalLine, Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [real_inner_eq_re_inner]

theorem coordinate_projector_gap (Q : ℂ →L[ℝ] ℂ) :
    (1 / 2 : ℝ) ≤ max ‖Q - horizontalNormal‖ ‖Q - verticalNormal‖ := by
  have hnorm := (horizontalNormal - verticalNormal).le_opNorm (1 : ℂ)
  simp only [sub_apply, horizontalNormal_one, verticalNormal_one,
    zero_sub, norm_neg, norm_one, mul_one] at hnorm
  have htriangle : ‖horizontalNormal - verticalNormal‖ ≤
      ‖Q - horizontalNormal‖ + ‖Q - verticalNormal‖ := by
    calc
      _ = ‖(horizontalNormal - Q) + (Q - verticalNormal)‖ := by congr 1; abel
      _ ≤ ‖horizontalNormal - Q‖ + ‖Q - verticalNormal‖ := norm_add_le _ _
      _ = ‖Q - horizontalNormal‖ + ‖Q - verticalNormal‖ := by rw [norm_sub_rev horizontalNormal Q]
  have h1 := le_max_left ‖Q - horizontalNormal‖ ‖Q - verticalNormal‖
  have h2 := le_max_right ‖Q - horizontalNormal‖ ‖Q - verticalNormal‖
  linarith

theorem cross_near_point_membership {δ : ℝ} (hδ : 0 < δ) (w : ℂ)
    (hw : dist w crossPoint < crossSmall δ / 5) :
    w ∈ ball crossPoint (crossRadius δ crossPoint) ∧ w ∈ ball (0 : ℂ) (crossRadius δ 0) := by
  have hs := (cross_parameters hδ).2.2.2.1
  have hs1 := (cross_parameters hδ).2.2.2.2.1
  constructor
  · rw [mem_ball, crossRadius_point hδ]
    linarith
  · rw [mem_ball, crossRadius_zero hδ]
    have ht := dist_triangle w crossPoint (0 : ℂ)
    have hp : dist crossPoint (0 : ℂ) = (3 / 4 : ℝ) := by
      norm_num [crossPoint, dist_eq_norm, Complex.norm_real]
    rw [hp] at ht
    linarith

theorem cross_no_common_operator (δ : ℝ) :
    ¬ ∃ (w : ℂ) (Q : ℂ →L[ℝ] ℂ), dist w crossPoint < crossSmall δ / 5 ∧
      ‖Q - horizontalNormal‖ ≤ 1 / 10 ∧ ‖Q - verticalNormal‖ ≤ 1 / 10 := by
  rintro ⟨w, Q, hw, hQ0, hQp⟩
  have h := coordinate_projector_gap Q
  have hm : max ‖Q - horizontalNormal‖ ‖Q - verticalNormal‖ ≤ (1 / 10 : ℝ) :=
    max_le hQ0 hQp
  linarith

theorem euclidean_coordinate_projector_gap
    (Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    (1 / 2 : ℝ) ≤ max
      ‖Q - realPlaneIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (horizontalNormal.comp realPlaneIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖
      ‖Q - realPlaneIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (verticalNormal.comp realPlaneIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ := by
  let No := realPlaneIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (horizontalNormal.comp realPlaneIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let Np := realPlaneIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (verticalNormal.comp realPlaneIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hNo : No (realPlaneIso 1) = 0 := by simp [No, horizontalNormal_one]
  have hNp : Np (realPlaneIso 1) = realPlaneIso 1 := by simp [Np, verticalNormal_one]
  have hn : ‖realPlaneIso 1‖ = 1 := by rw [realPlaneIso.norm_map]; norm_num
  have hg := (No - Np).le_opNorm (realPlaneIso 1)
  simp only [sub_apply, hNo, hNp, zero_sub, norm_neg, hn, mul_one] at hg
  have ht : ‖No - Np‖ ≤ ‖Q - No‖ + ‖Q - Np‖ := by
    calc
      _ = ‖(No - Q) + (Q - Np)‖ := by congr 1; abel
      _ ≤ ‖No - Q‖ + ‖Q - Np‖ := norm_add_le _ _
      _ = ‖Q - No‖ + ‖Q - Np‖ := by rw [norm_sub_rev No Q]
  change (1 / 2 : ℝ) ≤ max ‖Q - No‖ ‖Q - Np‖
  have h1 := le_max_left ‖Q - No‖ ‖Q - Np‖
  have h2 := le_max_right ‖Q - No‖ ‖Q - Np‖
  linarith

theorem realPlaneIso_cross_near {δ : ℝ} (hδ : 0 < δ)
    (w : EuclideanSpace ℝ (Fin 2))
    (hw : dist w (realPlaneIso crossPoint) < crossSmall δ / 5) :
    w ∈ ball (realPlaneIso crossPoint) (crossRadius δ crossPoint) ∧
      w ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (crossRadius δ 0) := by
  have h := cross_near_point_membership hδ (realPlaneIso.symm w) (by
    simpa only [← realPlaneIso.dist_map, realPlaneIso.apply_symm_apply] using hw)
  constructor
  · simpa only [mem_ball, ← realPlaneIso.dist_map, realPlaneIso.apply_symm_apply] using h.1
  · simpa only [mem_ball, ← realPlaneIso.dist_map, realPlaneIso.apply_symm_apply,
      map_zero] using h.2

theorem cross_cloud_counterexample {δ : ℝ} (hδ : 0 < δ) :
    IsCompact (crossSet δ) ∧ crossCentres ⊆ crossSet δ ∧
      0 < crossSmall δ ∧ crossSmall δ < 1 / 10000 ∧
      (∀ z : ℂ, crossSmall δ ≤ crossRadius δ z ∧ crossRadius δ z ≤ 1) ∧
      LipschitzWith 2 (crossRadius δ) ∧ crossRadius δ 0 = 1 ∧
      crossRadius δ crossPoint = crossSmall δ ∧
      (∀ x ∈ crossSet δ, ∀ y ∈ crossSet δ,
        |crossRadius δ y - crossRadius δ x| ≤ 2 * (dist x y + crossRadius δ x)) ∧
      (∀ x : crossCentres, Module.finrank ℝ (crossPlane x) = 1) ∧
      (∀ x : crossCentres,
        hausdorffEDist (crossSet δ ∩ ball (x : ℂ) (crossRadius δ x / δ))
          ((AffineSubspace.mk' (x : ℂ) (crossPlane x) : Set ℂ) ∩
            ball (x : ℂ) (crossRadius δ x / δ)) ≤ ENNReal.ofReal (δ * crossRadius δ x)) ∧
      (∀ w : ℂ, dist w crossPoint < crossSmall δ / 5 →
        w ∈ ball crossPoint (crossRadius δ crossPoint) ∧
          w ∈ ball (0 : ℂ) (crossRadius δ 0)) ∧
      ¬ ∃ (w : ℂ) (Q : ℂ →L[ℝ] ℂ), dist w crossPoint < crossSmall δ / 5 ∧
        ‖Q - horizontalNormal‖ ≤ 1 / 10 ∧ ‖Q - verticalNormal‖ ≤ 1 / 10 := by
  obtain ⟨hcompact, hsubset, hs, hs1, hbounds, hlip, ho, hp, hscale⟩ := cross_packet_bounds hδ
  obtain ⟨hdim, htests⟩ := cross_cloud_tests hδ
  exact ⟨hcompact, hsubset, hs, hs1, hbounds, hlip, ho, hp, hscale, hdim, htests,
    cross_near_point_membership hδ, cross_no_common_operator δ⟩

theorem no_full_ball_operator_field {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ D : ℂ → ℂ →L[ℝ] ℂ,
      (∀ w ∈ ball (0 : ℂ) (crossRadius δ 0), ‖D w - horizontalNormal‖ ≤ 1 / 10) ∧
        ∀ w ∈ ball crossPoint (crossRadius δ crossPoint), ‖D w - verticalNormal‖ ≤ 1 / 10 := by
  rintro ⟨D, h0, hp⟩
  have hnear : dist crossPoint crossPoint < crossSmall δ / 5 := by
    rw [dist_self]
    exact div_pos (cross_parameters hδ).2.2.2.1 (by norm_num)
  have hm := cross_near_point_membership hδ crossPoint hnear
  have hg := coordinate_projector_gap (D crossPoint)
  have hbound := max_le (h0 crossPoint hm.2) (hp crossPoint hm.1)
  linarith

end GC.MetricGeometry.CloudCounterexample
