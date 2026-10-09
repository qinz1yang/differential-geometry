import DifferentialGeometry.Geometry.Metric.Approximation.PlaneReferenceChart

/-!
# Actual plane charts at an anchor-compatible source radius

The chart's full target rectangle permits a source radius up to `Δ/20`. This
keeps the prescribed `Δ/40` anchors inside the actual KL source without the
larger numerical loss of the scale-100 metric supplier.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [mX : MetricSpace X]
variable {Q : X → WithLp 2 (ℝ × ℝ)} {p x : X} {Δ τ ν q : ℝ}

theorem exists_planeComparison_at_radius (hΔ : 0 < Δ) (hν : 0 < ν) (hν1 : ν < 1)
    (hq : 0 < q) (hτ : τ ≤ 1 / 10000) (hradius : q * ν⁻¹ ≤ Δ / 20)
    (herror : 4 * (τ * Δ) < q * ν) (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ →
      z.snd ∈ Icc 0 (100 * Δ) → ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd)
    (hhigh : (Q x).snd ≤ 102 / 10 * Δ) :
    letI := mX.rescale q⁻¹ (inv_pos.mpr hq)
    ∃ F : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) ν,
      ∀ y, F.toFun y = @planeComparisonMap X mX Q p x Δ q y := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hx200 : x ∈ ball p (200 * Δ) := ball_subset_ball (by linarith) hx
  have he0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have he : q⁻¹ * (τ * Δ) < ν / 4 := by
    rw [← div_eq_inv_mul, div_lt_iff₀ hq]
    nlinarith [herror]
  have hsource (y : X) (hy : q⁻¹ * dist y x < ν⁻¹) : y ∈ ball p (200 * Δ) := by
    have hyr : dist y x < q * ν⁻¹ := by
      rw [← div_eq_inv_mul, div_lt_iff₀ hq] at hy
      simpa only [mul_comm] using hy
    exact lt_of_le_of_lt (dist_triangle y x p) (by
      linarith [Metric.mem_ball.mp hx])
  have hmap (y : X) (hy : y ∈ ball p (200 * Δ)) :
      planeComparisonMap Q p x Δ q y = q⁻¹ • (Q y - Q x) :=
    planeComparisonMap_of_mem hy
  let := mX.rescale q⁻¹ (inv_pos.mpr hq)
  have hd (y z : X) : dist y z = q⁻¹ * @dist X mX.toDist y z :=
    MetricSpace.rescale_dist mX q⁻¹ (inv_pos.mpr hq) y z
  refine ⟨⟨hν, hν1, @planeComparisonMap X mX Q p x Δ q, ?_, ?_, ?_⟩,
    fun y => rfl⟩
  · rw [hmap x hx200, sub_self, smul_zero]
    rfl
  · intro y hy z hz
    have hym := hsource y (by rw [← hd]; exact hy)
    have hzm := hsource z (by rw [← hd]; exact hz)
    rw [hmap y hym, hmap z hzm, dist_smul₀, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hq), dist_sub_right, hd, ← mul_sub,
      abs_mul, abs_of_pos (inv_pos.mpr hq)]
    exact (mul_le_mul_of_nonneg_left (hdist y hym z hzm) (inv_pos.mpr hq).le).trans
      (by linarith)
  · intro z hz
    have hn : ‖z‖ < ν⁻¹ - ν := by simpa only [show (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) :
      WithLp 2 (ℝ × ℝ)) = 0 from rfl, dist_zero_right] using hz
    have hqz : ‖q • z‖ ≤ Δ / 20 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
      have hz' : ‖z‖ < ν⁻¹ := by linarith
      exact (mul_lt_mul_of_pos_left hz' hq).le.trans hradius
    obtain ⟨hf, hs, hnorm⟩ := planeComparison_target_mem_rectangle (mX := mX)
      hΔ hτ hQp hdist hx hlow hhigh hqz
    obtain ⟨y, hy, himage⟩ := hcover (Q x + q • z) hf hs
    have htarget : dist z (@planeComparisonMap X mX Q p x Δ q y) ≤ ν := by
      have heq : z = q⁻¹ • ((Q x + q • z) - Q x) := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
      rw [heq, hmap y hy, dist_smul₀, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hq), dist_sub_right, dist_comm]
      exact (mul_le_mul_of_nonneg_left himage (inv_pos.mpr hq).le).trans
        (by linarith)
    have hdy : @dist X mX.toDist y x ≤ q * ‖z‖ + 2 * (τ * Δ) := by
      have he := (abs_le.mp (hdist y hy x hx200)).1
      have ht := dist_triangle (Q y) (Q x + q • z) (Q x)
      rw [dist_eq_norm (Q x + q • z) (Q x), add_sub_cancel_left,
        norm_smul, Real.norm_eq_abs, abs_of_pos hq] at ht
      linarith
    have hym : y ∈ ball x ν⁻¹ := by
      change dist y x < ν⁻¹
      rw [hd]
      calc q⁻¹ * @dist X mX.toDist y x ≤ q⁻¹ * (q * ‖z‖ + 2 * (τ * Δ)) :=
            mul_le_mul_of_nonneg_left hdy (inv_pos.mpr hq).le
        _ = ‖z‖ + 2 * (q⁻¹ * (τ * Δ)) := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
            ring
        _ < ν⁻¹ := by linarith
    exact (infDist_le_dist_of_mem (mem_image_of_mem _ hym)).trans htarget

theorem exists_planeComparison_anchor_in_source (hΔ : 0 < Δ) (hq : 0 < q)
    (hτ : τ ≤ 1 / 10000) (hradius : Δ / 40 + 2 * (τ * Δ) < q * ν⁻¹)
    (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ →
      z.snd ∈ Icc 0 (100 * Δ) → ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd)
    (hhigh : (Q x).snd ≤ 102 / 10 * Δ) {v : WithLp 2 (ℝ × ℝ)} (hv : ‖v‖ ≤ Δ / 40) :
    ∃ a ∈ ball p (20 * Δ), dist (Q a) (Q x + v) ≤ τ * Δ ∧
      q⁻¹ * dist a x < ν⁻¹ := by
  obtain ⟨a, ha, he⟩ := exists_planeComparison_anchor
    hΔ hτ hQp hdist hcover hx hlow hhigh hv
  refine ⟨a, ha, he, ?_⟩
  have ha200 := ball_subset_ball (by linarith : 20 * Δ ≤ 200 * Δ) ha
  have hx200 := ball_subset_ball (by linarith : 15 * Δ ≤ 200 * Δ) hx
  have hd := (abs_le.mp (hdist a ha200 x hx200)).1
  have ht := dist_triangle (Q a) (Q x + v) (Q x)
  rw [dist_eq_norm (Q x + v) (Q x), add_sub_cancel_left] at ht
  rw [← div_eq_inv_mul, div_lt_iff₀ hq]
  linarith

theorem exists_planeComparison_at_radius_unscaled (hΔ : 0 < Δ)
    (hν : 0 < ν) (hν1 : ν < 1) (hτ : τ ≤ 1 / 10000)
    (hradius : ν⁻¹ ≤ Δ / 20) (herror : 4 * (τ * Δ) < ν) (hQp : Q p = 0)
    (hdist : ∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
      |dist (Q y) (Q z) - dist y z| ≤ τ * Δ)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ →
      z.snd ∈ Icc 0 (100 * Δ) → ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ)
    (hx : x ∈ ball p (15 * Δ)) (hlow : 8 / 100 * Δ ≤ (Q x).snd)
    (hhigh : (Q x).snd ≤ 102 / 10 * Δ) :
    ∃ F : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) ν,
      ∀ y, F.toFun y = planeComparisonMap Q p x Δ 1 y := by
  have hmetric : mX.rescale (1 : ℝ)⁻¹ (inv_pos.mpr zero_lt_one) = mX := by
    apply MetricSpace.ext
    ext y z
    simp only [MetricSpace.rescale_dist, inv_one, one_mul]
  have hf := exists_planeComparison_at_radius (q := 1) hΔ hν hν1 zero_lt_one hτ
    (by simpa only [one_mul] using hradius) (by simpa only [one_mul] using herror)
    hQp hdist hcover hx hlow hhigh
  rw [hmetric] at hf
  exact hf

end GC.MetricGeometry
