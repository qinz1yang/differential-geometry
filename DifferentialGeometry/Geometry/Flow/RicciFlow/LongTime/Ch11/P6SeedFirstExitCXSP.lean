import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6EndpointWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FirstExitWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4

set_option autoImplicit false

/-!
# CX-SPINE G6：由局部时间/梯度控制实际生产单 slab 种子不出界

在尚未出界的窗口中，截断倒数 ODE 给中心 R≤2MQ，局部梯度给 ℓ 球 R≤8MQ；
种子 K0 与 Hamilton–Ivey 则给两端 Ricci。将其喂有窗口记忆的首次接触引理。
不要求全窗事先位于种子球，不引入外部 hscalU；跨 surgery 和更大的固定 U 仍需另证。
保留任意 Q>0 与 Q*a≥1；终端 R≤M*Q，故可直接在原种子尺度使用。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 真正从局部微分控制产生单 slab 的种子距离控制与严格不出界。 -/
theorem ObservedHistory.seed_firstExit_of_local_controls_CXSP (H : ObservedHistory.{u})
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
    {a t M Q K ℓ q : ℝ} {Ctime Cgrad : ℝ≥0} {X : ℝ≥0∞}
    (hQ : 0 < Q) (ha : 1 ≤ Q * a) (hat : a ≤ t) (hja : H.time j.castSucc < a)
    (htj : t < H.time j.succ) (hseedA : (aSeed : ℝ) ≤ a) (htT : t ≤ Tn)
    (hM : 0 < M) (hqM : q ≤ M * Q)
    (hscalar : (H.event j).incoming.flow.scalar t x ≤ M * Q)
    (htime : Ctime * (M * Q) * (t - a) ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * (M * Q)) ≤ 1 / 4)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4)) * Q ≤ K)
    (hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (t - a)) < X)
    (hderiv : ∀ u ∈ Ioo a t,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x < X →
      q < (H.event j).incoming.flow.scalar u x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic u) u| ≤
        Ctime * (H.event j).incoming.flow.scalar u x ^ 2)
    (hgrad : ∀ u ∈ Ioo a t,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x < X →
      ∀ z ∈ riemannianBallOf ((H.event j).incoming.flow.base.metric u) x (2 * ℓ),
      q < (H.event j).incoming.flow.scalar u z → ∀ ξ : TangentSpace ThreeModel z,
        |scalarDifferential (H.event j).incoming.flow u z ξ| ≤
          Cgrad * (H.event j).incoming.flow.scalar u z *
            Real.sqrt ((H.event j).incoming.flow.scalar u z) *
            Real.sqrt (((H.event j).incoming.flow.base.metric u).inner z ξ ξ)) :
    ∀ u ∈ Icc a t,
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x < X ∧
      riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal ((8 / ℓ) * (t - u)) := by
  have hRic : ∀ s ∈ Icc a t,
      (∀ u ∈ Ioo s t,
        riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
          (seedTrace.point j.castSucc h1 h2) x < X) →
      ∀ u ∈ Ioo s t, ∀ z : (H.stage j.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf ((H.event j).incoming.flow.base.metric u)
          (seedTrace.point j.castSucc h1 h2) z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((H.event j).incoming.flow.base.metric u) x z < ENNReal.ofReal ℓ) →
      ricciTensor ((H.event j).incoming.flow.base.metric u) z ξ ξ ≤
        (3 / ℓ ^ 2) * ((H.event j).incoming.flow.base.metric u).inner z ξ ξ := by
    intro s hs hstay
    have htimeS : Ctime * (M * Q) * (t - s) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 t)
        (mul_nonneg Ctime.coe_nonneg (mul_pos hM hQ).le)).trans htime
    have hball := (H.event j).incoming.scalar_le_eight_mul_on_window_ball_CXSP x
      (hja.le.trans hs.1) hs.2 htj
      (fun u hu => hderiv u ⟨hs.1.trans_lt hu.1, hu.2⟩ (hstay u hu))
      (fun u hu => hgrad u ⟨hs.1.trans_lt hu.1, hu.2⟩ (hstay u hu))
      (mul_pos hM hQ) hqM hscalar htimeS hℓ hspace
    intro u hu z ξ hz
    have hAu : a ≤ u := hs.1.trans hu.1.le
    exact H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin j h1 h2 x
      (Q := Q) (K := K) (C := 8 * M) (ℓ := ℓ) (s := u)
      hQ hℓ hKℓ hℓr hKr (by positivity)
      (by simpa only [show 8 * M / 2 = 4 * M by ring] using hKC)
      (hja.trans_le hAu) (hu.2.trans htj) (hseedA.trans hAu) (hu.2.le.trans htT)
      (ha.trans (mul_le_mul_of_nonneg_left hAu hQ.le))
      (fun y hy => by simpa only [mul_assoc] using hball u hu y hy.le) z ξ hz
  have hdist := H.firstExit_distance_of_window_ricci_CXSP j hℓ hat hja htj
    (seedTrace.point j.castSucc h1 h2) x hmargin hRic
  intro u hu
  have hbound := hdist u hu
  have hdrift : (8 / ℓ) * (t - u) ≤ (8 / ℓ) * (t - a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hu.1 t) (by positivity)
  exact ⟨hbound.trans_lt
    ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdrift)).trans_lt hmargin), hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
