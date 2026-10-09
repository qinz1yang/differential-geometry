import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedIntervalTargetRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.RayTargetRescaling

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

private theorem strong_edge_product_budgets {Δ β βE c d : ℝ}
    (hΔ : 1 ≤ Δ) (hβ : 0 < β) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2) (hd : d ≤ 13 * Δ) :
    3 * c * β ≤ βE ∧ d + βE⁻¹ / c + 2 * β ≤ β⁻¹ ∧ d < β⁻¹ ∧ β < 1 := by
  have hE : 0 < βE := by linarith only [hβ, hβsmall]
  have hc0 : 0 < c := by linarith only [hc.1]
  have hden : 0 < 100 * Δ + 100 / βE := by positivity
  have hlarge : 100 * Δ + 100 / βE < β⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hβ).mpr
    nlinarith only [(lt_div_iff₀ hden).mp hβdomain]
  have hβone : β < 1 := by linarith only [hβsmall, hβE]
  have hratio : βE⁻¹ / c ≤ 2 / βE := by
    apply (div_le_iff₀ hc0).mpr
    have hh := mul_le_mul_of_nonneg_left hc.1 (show 0 ≤ 2 / βE by positivity)
    rw [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  have hEinv : 0 < βE⁻¹ := inv_pos.mpr hE
  simp only [div_eq_mul_inv] at hlarge hratio ⊢
  refine ⟨?_, ?_, ?_, hβone⟩
  · have hh := mul_le_mul_of_nonneg_left hc.2 (show 0 ≤ 3 * β by positivity)
    nlinarith only [hh, hβsmall, hβ]
  · linarith only [hd, hratio, hlarge, hβone, hΔ, hEinv]
  · linarith only [hd, hlarge, hΔ, hEinv]

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [mY : MetricSpace Y]
variable {p a : X} {q : Y} {Δ β βE s ε c e θ : ℝ}

private theorem residual_radius_le {F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β}
    (ha : dist a p < β⁻¹) : dist (F.toFun a).snd q ≤ dist a p + β := by
  have hcoord := WithLp.dist_snd_le (F.toFun a) (WithLp.toLp 2 ((0 : ℝ), q))
  have hrad := (abs_le.mp (F.radial_error a ha)).2
  change dist (F.toFun a).snd q ≤ dist (F.toFun a) (WithLp.toLp 2 ((0 : ℝ), q)) at hcoord
  linarith only [hcoord, hrad]

theorem isEdgePoint_of_marked_interval_model {C : ℝ} {o : Icc (0 : ℝ) C}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o ε)
    (hΔ : 1 ≤ Δ) (hC : 500 * Δ < C) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hεs : ε ≤ s / 1000) (hεΔ : ε ≤ 1 / (100000 * Δ))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2) (ha : dist a p ≤ 13 * Δ) (ho : o.val ≤ Δ / 2)
    (he : e ≤ s / 1000) (hθ : θ ≤ s / 1000)
    (hheight : (G.toFun (F.toFun a).snd).val ≤ 2 * e + θ) :
    let hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc.1
    let : MetricSpace X := mX.rescale c hc0
    isEdgePoint.{u, v} a Δ βE s := by
  have hc0 : 0 < c := by linarith only [hc.1]
  obtain ⟨hFerror, hFdomain, hFa, hβone⟩ :=
    strong_edge_product_budgets hΔ F.error_pos hβE hβsmall hβdomain hc ha
  have hfactor : dist (F.toFun a).snd q ≤ 13 * Δ + 1 :=
    (residual_radius_le (F := F) hFa).trans (by linarith only [ha, hβone])
  let F' := F.recenterRescaleRealProduct a hc0 hFerror (by linarith only [hβE]) hFdomain
  obtain ⟨hD, G', hlength, _, _⟩ := G.exists_strong_edge_interval_model (F.toFun a).snd
    hΔ hC hs hssmall hεs hεΔ hc hfactor ho he hθ hheight
  let qa := (F.toFun a).snd
  let : MetricSpace X := mX.rescale c hc0
  exact ⟨Y, mY.rescale c hc0, qa, c * C, hD, hlength, ⟨F'⟩, ⟨G'⟩⟩

theorem isEdgePoint_of_ray_model {o : Ici (0 : ℝ)}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o ε)
    (hΔ : 1 ≤ Δ) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hεs : ε ≤ s / 1000) (hεΔ : ε ≤ 1 / (100000 * Δ))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2) (ha : dist a p ≤ 13 * Δ) (ho : o.val ≤ Δ / 2)
    (he : e ≤ s / 1000) (hθ : θ ≤ s / 1000)
    (hheight : (G.toFun (F.toFun a).snd).val ≤ 2 * e + θ) :
    let hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc.1
    let : MetricSpace X := mX.rescale c hc0
    isEdgePoint.{u, v} a Δ βE s := by
  have hc0 : 0 < c := by linarith only [hc.1]
  obtain ⟨hFerror, hFdomain, hFa, hβone⟩ :=
    strong_edge_product_budgets hΔ F.error_pos hβE hβsmall hβdomain hc ha
  have hfactor : dist (F.toFun a).snd q ≤ 13 * Δ + 1 :=
    (residual_radius_le (F := F) hFa).trans (by linarith only [ha, hβone])
  let F' := F.recenterRescaleRealProduct a hc0 hFerror (by linarith only [hβE]) hFdomain
  obtain ⟨hD, G', hlength, _, _⟩ := G.exists_strong_edge_ray_model (F.toFun a).snd
    hΔ hs hssmall hεs hεΔ hc hfactor ho he hθ hheight
  let qa := (F.toFun a).snd
  let : MetricSpace X := mX.rescale c hc0
  exact ⟨Y, mY.rescale c hc0, qa, max (201 * Δ) (4 / s), hD, hlength, ⟨F'⟩, ⟨G'⟩⟩

end GC.MetricGeometry
