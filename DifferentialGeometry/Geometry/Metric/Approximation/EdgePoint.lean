import DifferentialGeometry.Geometry.Metric.Approximation.RealProductRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.IntervalTargetRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeRescalingBounds
import DifferentialGeometry.Geometry.Metric.Scaling.LipschitzScale

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

universe u v
variable {X : Type u} [mX : MetricSpace X]

def isEdgePoint (p : X) (Δ β σ : ℝ) : Prop :=
  ∃ (Y : Type v) (mY : MetricSpace Y), letI := mY
    ∃ (q : Y) (C : ℝ) (hC : 0 ≤ C), 200 * Δ < C ∧
      Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β) ∧
      Nonempty (KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) σ)

theorem isEdgePoint_of_recentered_interval {Y : Type v} [mY : MetricSpace Y]
    {p : X} {q : Y} {Δ C β σ β' σ' c : ℝ} (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) σ)
    (a : X) (hc : 0 < c) (hβ' : β' < 1) (hσ' : 0 < σ') (hσ'one : σ' < 1)
    (hlength : 200 * Δ ≤ C) (hcontraction : 200 * Δ * (1 - c) ≤ σ' / 100)
    (hFerror : 3 * c * β ≤ β') (hFdomain : dist a p + β'⁻¹ / c + 2 * β ≤ β⁻¹)
    (hGdomain : dist (F.toFun a).snd q + σ'⁻¹ / c + 2 * σ ≤ σ⁻¹)
    (hGerror : 2 * c * dist (F.toFun a).snd q + 3 * c * σ ≤ σ' / 2) :
    let : MetricSpace X := mX.rescale c hc
    isEdgePoint.{u, v} a Δ β' σ' := by
  let qa := (F.toFun a).snd
  let F' := F.recenterRescaleRealProduct a hc hFerror hβ' hFdomain
  have hG := G.exists_recenterRescaleInterval_strict hC (F.toFun a).snd hc hσ' hσ'one
    hlength hcontraction hGdomain hGerror
  obtain ⟨L, hL, hstrict, _, G', _, _⟩ := hG
  let : MetricSpace X := mX.rescale c hc
  refine ⟨Y, mY.rescale c hc, qa, L, hL, hstrict, ⟨F'⟩, ⟨G'⟩⟩

theorem isEdgePoint_of_lipschitz_scale {Y : Type v} [MetricSpace Y]
    {p a : X} {q : Y} {Δ C β σ β' σ' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1) (hρa : 0 < ρ a)
    (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) σ)
    (hβ' : 0 < β') (hσ' : 0 < σ')
    (hsmallβ' : β' < 1 / 10000) (hsmallσ' : σ' < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < σ' / (100000000 * Δ ^ 2))
    (hβΔ : β' < 1 / (1000000 * Δ))
    (hσβ : σ < β' / 100000) (hσσ : σ < σ' / 100000)
    (hβσ : β < σ / 100000) (hββ : β < β' / 100000)
    (hlength : 200 * Δ ≤ C) (ha : dist a p ≤ 101 * Δ)
    (hqa : dist (F.toFun a).snd q < 2 * β) :
    let : MetricSpace X := mX.rescale (ρ a)⁻¹ (inv_pos.mpr hρa)
    isEdgePoint.{u, v} a Δ β' σ' := by
  have hclose : |ρ a - 1| ≤ 101 * Δ * Λ := by
    have hh := abs_scale_ratio_sub_one_le hρ (p := p) (a := a) (by rw [hρp]; norm_num)
    rw [hρp, div_one, div_one] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left ha Λ.coe_nonneg])
  obtain ⟨_, _, hFerror, hFdomain, hcontraction, hGdomain, hGerror⟩ :=
    edge_recenter_rescale_budgets hΔ Λ.coe_nonneg hρa F.error_pos G.error_pos
      hβ' hσ' hsmallβ' hsmallσ' hscale hend hβΔ hσβ hσσ hβσ hββ hclose
      dist_nonneg ha dist_nonneg hqa
  exact isEdgePoint_of_recentered_interval hC F G a (inv_pos.mpr hρa)
    (by linarith) hσ' (by linarith) hlength hcontraction hFerror hFdomain hGdomain hGerror

end GC.MetricGeometry
