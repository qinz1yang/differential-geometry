import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedBallFootprintCXSP

set_option autoImplicit false

/-!
# CX-SPINE G30：canonical 二次开单位球的实际 scalar 与 seed 距离界

只消费 witness 的 radius_lower/ball_inside/scalar_bounds，不扩大到闭球。
Q(L−1)<Rsecondary<Q(L+1) 与 L≥3 支付缩小半径和固定 m=C*L 的标量预算。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 实际 canonical witness 给二次单位开球的 mQ 上界；不索取 capTube 或闭球 bound。 -/
theorem secondary_unit_ball_scalar_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {y : P.Carrier} {eps C1 C2 C L Q : ℝ}
    (W : SpatialCanonicalWitness g eps C1 C2 y)
    (hC : 1 ≤ C) (hC2 : 2 * C2 ≤ C) (hL : 3 ≤ L) (hQ : 0 < Q)
    (hupper : metricScalarAt g y < Q * (L + 1)) :
    1 / 2 ≤ C * L ∧
      ∀ z ∈ riemannianBallOf g y (Real.sqrt (metricScalarAt g y))⁻¹,
        metricScalarAt g z ≤ (C * L) * Q := by
  have hL0 : 0 ≤ L := by linarith
  have hC20 : 0 ≤ C2 := (by norm_num : (0 : ℝ) ≤ 1).trans W.one_le_comparison_constant
  have hCL : L ≤ C * L := by nlinarith only [mul_le_mul_of_nonneg_right hC hL0]
  refine ⟨by linarith only [hCL, hL], ?_⟩
  intro z hz
  have hscalar := (W.scalar_bounds z
    (W.ball_inside (riemannianBallOf_mono _ _ W.radius_lower hz))).2
  calc
    metricScalarAt g z ≤ C2 * metricScalarAt g y := hscalar
    _ ≤ C2 * (Q * (L + 1)) := mul_le_mul_of_nonneg_left hupper.le hC20
    _ ≤ (2 * C2) * (L * Q) := by
      have hm := mul_le_mul_of_nonneg_left (by linarith : L + 1 ≤ 2 * L)
        (mul_nonneg hC20 hQ.le)
      nlinarith only [hm]
    _ ≤ C * (L * Q) := mul_le_mul_of_nonneg_right hC2 (mul_nonneg hL0 hQ.le)
    _ = (C * L) * Q := by ring

/-- 二次球半径不超过 primary 单位半径，真实 center 余量给全部点的 seed 距离。 -/
theorem secondary_unit_ball_distance_CXSP
    {P : OrientedThreeStage.{u}} (g : P.Metric) {p y : P.Carrier}
    {H0 r L Rn dCenter d0 : ℝ} (hH : 0 < H0) (hr : 0 < r) (hL : 3 ≤ L)
    (hlower : (H0 * (r ^ 2)⁻¹) * (L - 1) < Rn)
    (hdCenter : 0 ≤ dCenter) (hfit : dCenter + 1 / Real.sqrt H0 ≤ d0)
    (hcenter : riemannianEDistOf g p y ≤ ENNReal.ofReal (dCenter * r)) :
    ∀ z ∈ riemannianBallOf g y (Real.sqrt Rn)⁻¹,
      riemannianEDistOf g p z ≤ ENNReal.ofReal (d0 * r) := by
  let Q := H0 * (r ^ 2)⁻¹
  have hQ : 0 < Q := mul_pos hH (inv_pos.mpr (sq_pos_of_pos hr))
  have hQR : Q ≤ Rn := by
    have hm := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ L - 1) hQ.le
    nlinarith only [hm, hlower]
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsR : 0 < Real.sqrt Rn := Real.sqrt_pos.mpr (hQ.trans_le hQR)
  have hradius : (Real.sqrt Rn)⁻¹ ≤ 1 / Real.sqrt Q := by
    rw [one_div]
    exact (inv_le_inv₀ hsR hsQ).mpr (Real.sqrt_le_sqrt hQR)
  intro z hz
  apply seed_closedBall_distance_CXSP g hH hr (by norm_num : (0 : ℝ) ≤ 1)
    hdCenter hfit hcenter z
  exact hz.le.trans (ENNReal.ofReal_le_ofReal hradius)

end GC.LongTime.Ch11
