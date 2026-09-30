import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem coverage_witness_radius {p : X} {q : Y} {β : ℝ}
    (F : KleinerLottApprox p q β) (y : Y) (hy : dist y q < β⁻¹ - β) :
    ∃ a ∈ ball p β⁻¹, dist y (F.toFun a) < 2 * β ∧ dist a p < dist y q + 3 * β := by
  obtain ⟨a, ha, hclose⟩ := F.coverage_witness y hy
  have hrad := (abs_le.mp (F.radial_error a ha)).1
  have htri := dist_triangle (F.toFun a) y q
  rw [dist_comm (F.toFun a) y] at htri
  exact ⟨a, ha, hclose, by linarith only [hrad, htri, hclose]⟩

theorem exists_product_lift_radius {p : X} {q : Y} {β : ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β) (t : ℝ) (z : Y)
    (hbuffer : |t| + dist z q + 3 * β < β⁻¹) :
    ∃ a : X, dist a p < |t| + dist z q + 3 * β ∧
      dist (F.toFun a) (WithLp.toLp 2 (t, z)) < 2 * β ∧
      dist (F.toFun a).snd z < 2 * β := by
  have hb := F.error_pos
  let y := WithLp.toLp 2 (t, z)
  have hradius : dist y (WithLp.toLp 2 ((0 : ℝ), q)) ≤ |t| + dist z q := by
    have htri := dist_triangle y (WithLp.toLp 2 ((0 : ℝ), z)) (WithLp.toLp 2 ((0 : ℝ), q))
    have h1 := (WithLp.isometry_prodMk_right (E := ℝ) z).dist_eq t 0
    have h2 := (WithLp.isometry_prodMk_left (Y := Y) (0 : ℝ)).dist_eq z q
    simpa only [y, h1, h2, Real.dist_eq, sub_zero] using htri
  obtain ⟨a, _, hclose, hrad⟩ := F.coverage_witness_radius y (by linarith)
  have hfactor := WithLp.dist_snd_le (F.toFun a) y
  change dist (F.toFun a).snd z ≤ dist (F.toFun a) y at hfactor
  rw [dist_comm y (F.toFun a)] at hclose
  exact ⟨a, by linarith only [hrad, hradius], hclose, hfactor.trans_lt hclose⟩

theorem exists_nearby_product_lift {p : X} {q : Y} {β Δ : ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (hΔ : 1 ≤ Δ) (hβΔ : β ≤ 1 / (1000 * Δ))
    (t : ℝ) (z : Y) (ht : |t| ≤ 12 * Δ) (hz : dist z q ≤ Δ / 2) :
    ∃ a : X, dist a p < |t| + dist z q + 3 * β ∧ dist a p < 13 * Δ ∧
      dist (F.toFun a) (WithLp.toLp 2 (t, z)) < 2 * β ∧
      dist (F.toFun a).snd z < 2 * β := by
  have hb := F.error_pos
  have hΔpos : 0 < Δ := by linarith
  have hprod : β * (1000 * Δ) ≤ 1 := (le_div_iff₀ (by positivity)).mp hβΔ
  have hb1 : β ≤ 1 / 1000 := by nlinarith only [hprod, hΔ, hb]
  have hsource : 13 * Δ < β⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hb).mpr
    nlinarith only [hprod]
  have hrad : |t| + dist z q + 3 * β < 13 * Δ := by linarith only [ht, hz, hb1, hΔ]
  obtain ⟨a, ha, hclose, hfactor⟩ := F.exists_product_lift_radius t z (hrad.trans hsource)
  exact ⟨a, ha, ha.trans hrad, hclose, hfactor⟩

end GC.MetricGeometry.KleinerLottApprox
