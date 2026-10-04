import DifferentialGeometry.Geometry.Metric.Approximation.LineUnitBallSplitting
import DifferentialGeometry.Geometry.Comparison.OutwardPrefixCalibration

/-!
# Exact annular anchors with a radial calibration budget

The auxiliary angle also satisfies θ ≤ σ/4. This retained choice allows LC69 to calibrate the
original radial distance, uniformly for all sufficiently large normalization factors.
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem exists_original_radial_exact_scale_anchors {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ δσ Λσ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ σ / 4 ∧ 0 < δσ ∧ 0 < Λσ ∧
      ∀ (X : Type u) (C : Type v) [MetricSpace X] [MetricSpace C],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (p : X) (o : C), RadialConeData o → ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < δσ → fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam : ℝ, Λσ ≤ lam →
      ∃ a b z : X,
        dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z) (dist p z) ∧
        dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
        dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
        π - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
          (lam * dist a b) := by
  obtain ⟨α, hα, hαone, hαbudget⟩ := exists_annular_strainer_angle hσ hσone
  let θ := min α (σ / 4)
  have hθ : 0 < θ := lt_min hα (by positivity)
  have hθα : θ ≤ α := min_le_left _ _
  have hθσ : θ ≤ σ / 4 := min_le_right _ _
  have hθone : θ ≤ 1 := hθα.trans hαone
  have hθbudget : 4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) *
      (1 - cos (θ / 2)) < 1 - cos σ := by
    have hc : cos (α / 2) ≤ cos (θ / 2) :=
      cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (by linarith [two_le_pi]) (by linarith)
    have hp : 0 ≤ 4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) := by positivity
    exact (mul_le_mul_of_nonneg_left (by linarith :
      1 - cos (θ / 2) ≤ 1 - cos (α / 2)) hp).trans_lt hαbudget
  have hcosθ : 0 < 1 - cos θ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hθ
    rw [cos_zero] at h
    linarith
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  refine ⟨θ, min (1 / 100) ((1 - cos θ) / 600), 20 * L, hθ, hθone, hθσ,
    lt_min (by norm_num) (by positivity), by positivity, ?_⟩
  intro X C _ _ hsegments p o H δ φ hδ hcomp q hq1 hq2 lam hlam
  have hseg' : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
    intro x y
    obtain ⟨f, _, h0, h1, hd⟩ := hsegments x y
    exact ⟨f, h0, h1, hd⟩
  have hδpos := φ.error_pos
  have hδ1 : δ < 1 / 100 := hδ.trans_le (min_le_left _ _)
  have hδ2 : δ < (1 - cos θ) / 600 := hδ.trans_le (min_le_right _ _)
  set D : ℝ := dist p q with hD
  have hDpos : 0 < D := by linarith
  -- LC25: the outward point at twice the radius.
  obtain ⟨q', hpq', hlow, hhigh⟩ := φ.exists_outward_point_on_annulus H hsegments
    (a := 1 / 10) (b := 10) (by norm_num) (by norm_num) (by linarith) (by linarith) ⟨hq1, hq2⟩
  -- The point `z` at distance `D` from `q` on a segment towards `q'`.
  obtain ⟨z, -, hqz, -, hzq', -, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q q' q' dist_nonneg hlow hlow
  have hpz_low : 2 * D - 15 * δ < dist p z := by
    have h := dist_triangle p z q'
    linarith
  have hpz_up : dist p z ≤ 2 * D := by
    have h := dist_triangle p q z
    linarith
  have hpz_nonneg : 0 ≤ dist p z := dist_nonneg
  have hqp : dist q p = D := dist_comm q p
  -- The angle at `q` of `(q; p, z)` at curvature `-(1/60)²`.
  have hangle0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist p z) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hDpos hpz_nonneg hpz_up
      (by nlinarith) hθ.le
    rw [div_lt_iff₀ hDpos]
    have : 4 * (2 * D - dist p z) < 60 * δ := by linarith
    nlinarith
  -- Shortening to the exact length `s = L / λ`.
  set s : ℝ := L / lam with hs
  have hlampos : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have hspos : 0 < s := div_pos hLpos hlampos
  have hs20 : s ≤ 1 / 20 := by
    rw [hs, div_le_iff₀ hlampos]
    linarith
  have hsD : s ≤ D := by linarith
  obtain ⟨a, b, hqa, hqb, hap, hbz, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q p z hspos.le
      (by rw [hqp]; exact hsD) (by rw [hqz]; exact hsD)
  have hmem (x : X) (hx : dist x p < 21) : x ∈ ball p 21 := hx
  have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
  have hqB : q ∈ ball p 21 := hmem q (by rw [hqp]; linarith)
  have hzB : z ∈ ball p 21 := hmem z (by rw [dist_comm]; linarith)
  have haB : a ∈ ball p 21 := hmem a (by rw [hap, hqp]; linarith)
  have hbB : b ∈ ball p 21 := hmem b (by
    have h := dist_triangle b q p
    rw [dist_comm b q, hqb, hqp] at h
    linarith)
  have hzq : z ≠ q := by
    intro h
    rw [h, dist_self] at hqz
    linarith
  have haq : a ≠ q := by
    intro h
    rw [h, dist_self] at hqa
    linarith
  have hκ : (0 : ℝ) ≤ (1 / 60) ^ 2 := by positivity
  have hsh1 := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hqB haB hpB hzB
    (by rw [hqa]; exact hspos) hzq (by rw [hqa, hap]; ring)
  have hsh2 := comparisonAngleNegCurvature_le_of_shortening_right hκ hcomp hqB hbB hzB haB
    (by rw [hqb]; exact hspos) haq (by rw [hqb, hbz]; ring)
  have hangle_s : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) s s (dist a b) := by
    have h0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z)
        (dist p z) := by rw [hqp, hqz]; exact hangle0
    have h := (h0.trans_le hsh1).trans_le hsh2
    rwa [hqa, hqb] at h
  have hab_up : dist a b ≤ 2 * s := by
    have h := dist_triangle a q b
    rw [dist_comm a q, hqa, hqb] at h
    linarith
  have hchord := two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature hκ hspos
    dist_nonneg hab_up hθ.le (by linarith [two_le_pi]) hangle_s
  -- The comparison angle in the rescaled distance at curvature `-σ`.
  have hlams : lam * s = L := by
    rw [hs]
    field_simp
  have hfinal := pi_sub_lt_comparisonAngle_of_scaled_chord hσ hθbudget
    hspos hlampos (by simpa only [hL] using hlams) hchord dist_nonneg hab_up
  refine ⟨a, b, z, hqz, by linarith, by rw [hqp, hqz]; exact hangle0, hqa, hqb,
    by rw [hqa, hap]; ring,
    by rw [hqb, hbz]; ring, ?_⟩
  rw [hqa, hqb]
  exact hfinal


end GC.MetricGeometry
