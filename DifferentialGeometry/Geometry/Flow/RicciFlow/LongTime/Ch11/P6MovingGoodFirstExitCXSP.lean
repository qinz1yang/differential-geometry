import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedFirstExitCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6MovingGoodControlsCXSP

set_option autoImplicit false

/-!
# CX-SPINE G7：移动种子球 Good 直接喂单 slab 首次接触

退出预算 B，小球半径 ℓ，Good 供给半径 ρ≥B+2ℓ。
将 Good 中的真实时间导数与 witness 梯度投到 incoming flow，三角不等式
支付所有 2ℓ 球的供给域，再调用 G6 实际首次接触消费者。
保持单 slab 与终端相对曲率界假设；没有用全窗 footprint 作前提。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 移动种子球内的完整 Good 供给实际推出单 slab 短窗不出界。 -/
theorem ObservedHistory.seed_firstExit_of_moving_good_CXSP (H : ObservedHistory.{u})
    {Tn aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage v) v) (a₀ + v) z)
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (x : (H.stage j.castSucc).Carrier)
    {a t M Q K ℓ q B ρ ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hQ : 0 < Q) (ha : 1 ≤ Q * a) (hat : a ≤ t) (hja : H.time j.castSucc < a)
    (htj : t < H.time j.succ) (hseedA : (aSeed : ℝ) ≤ a) (htT : t ≤ Tn)
    (hM : 0 < M) (hqM : q ≤ M * Q)
    (hscalar : (H.event j).incoming.flow.scalar t x ≤ M * Q)
    (htime : Ctime * (M * Q) * (t - a) ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hspace : (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * (M * Q)) ≤ 1 / 4)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4)) * Q ≤ K)
    (hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (t - a)) <
      ENNReal.ofReal B)
    (hregion : B + 2 * ℓ ≤ ρ) (hC2 : 0 ≤ C2)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ Tn),
      a ≤ (v : ℝ) → (v : ℝ) ≤ t →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvT)) ρ,
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v y) :
    ∀ u ∈ Icc a t,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x < ENNReal.ofReal B ∧
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (t - u)) := by
  have hcontrols := H.incoming_controls_of_moving_good_CXSP haT seedTrace hgood
    j h1 h2 hja htj hseedA htT
  have hB : 0 < B := ENNReal.ofReal_pos.mp (bot_le.trans_lt hmargin)
  have hBρ : B ≤ ρ := (le_add_of_nonneg_right (by positivity)).trans hregion
  refine H.seed_firstExit_of_local_controls_CXSP haT hsmall hclock seedTrace ha₀ hpin
    j h1 h2 x hQ ha hat hja htj hseedA htT hM hqM hscalar htime hℓ hspace
    hKℓ hℓr hKr hKC hmargin ?_ ?_
  · intro u hu hd hR
    exact (hcontrols u hu x (hd.trans_le (ENNReal.ofReal_le_ofReal hBρ)) hR).1
  · intro u hu hd z hz hR ξ
    have hsum : ENNReal.ofReal B + ENNReal.ofReal (2 * ℓ) ≤ ENNReal.ofReal ρ := by
      rw [← ENNReal.ofReal_add hB.le (by positivity)]
      exact ENNReal.ofReal_le_ofReal hregion
    have hball : z ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) ρ :=
      (riemannianEDistOf_triangle _ _ x z).trans_lt ((ENNReal.add_lt_add hd hz).trans_le hsum)
    simpa only [Real.coe_toNNReal _ hC2] using (hcontrols u hu z hball hR).2 ξ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
