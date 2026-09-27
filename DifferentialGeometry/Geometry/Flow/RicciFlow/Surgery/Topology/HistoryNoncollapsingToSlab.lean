import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable (H : ObservedHistory.{u})

private theorem volume_ge_of_stage_window {κ r : ℝ} (t : Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hk : H.activeStage t = k) (p : (H.stage k).Carrier)
    (hr : 0 < r) (hwin : H.time k ≤ (t : ℝ) - r ^ 2)
    (hbound : ∀ v ∈ Icc ((t : ℝ) - r ^ 2) t,
      ∀ x ∈ riemannianBallOf (H.stageMetric k t) p r,
        r ^ 4 * Tensor0SBundle.normSq0S (H.stageMetric k v) x 4
          (metricRm04At (H.stageMetric k v) x) ≤ 1)
    (hvol : ∀ q : (H.stageAt t).Carrier, H.isParabolicallyRmControlledBall t q r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) q r)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage k).Carrier (H.stageMetric k t)
        (riemannianBallOf (H.stageMetric k t) p r) := by
  subst hk
  have ht : H.time (H.activeStage t) < (t : ℝ) := by
    have : 0 < r ^ 2 := by positivity
    linarith
  let B : Perelman.FlowMetricBall (H.closedPrefixAt t ht).flow
      ⟨t, H.activeStage_time_le t, le_rfl⟩ := ⟨p, r, hr⟩
  have hB : B.IsParabolicallyRmControlled := by
    refine ⟨fun v hv => ?_, fun v hv x hx => ?_⟩
    · change H.time (H.activeStage t) ≤ v ∧ v ≤ (t : ℝ)
      exact ⟨hwin.trans hv.1, hv.2⟩
    · have hx' : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
        change x ∈ riemannianBallOf ((H.closedPrefixAt t ht).flow.base.metric t) p r at hx
        rwa [H.closedPrefixAt_metric] at hx
      have hb := hbound v hv x hx'
      change r ^ 4 * Tensor0SBundle.normSq0S ((H.closedPrefixAt t ht).flow.base.metric v) x 4
        (metricRm04At ((H.closedPrefixAt t ht).flow.base.metric v) x) ≤ 1
      rw [H.closedPrefixAt_metric]
      exact hb
  exact hvol p (H.isParabolicallyRmControlledBall_of_closedPrefixAt t ht B hB)

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}}

theorem isKappaNoncollapsed_of_noncollapsedBefore (H : RetainedCoreHistory P₀) {κ ρ t₀ : ℝ}
    (hκ : 0 < κ) (hnc : H.NoncollapsedBefore κ ρ t₀) (j : Fin H.eventCount)
    (τ : (RealTimeInterval.closedOpen _ _ (H.toHistory.event j).incoming.lt).FlowTime)
    (B : Perelman.FlowMetricBall (H.toHistory.event j).incoming.flow τ) :
    (τ : ℝ) ≤ t₀ → B.radius ≤ ρ → B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ := by
  intro hτt hrρ hB
  have hr := B.radius_pos
  have hwin : H.time j.castSucc ≤ (τ : ℝ) - B.radius ^ 2 :=
    (hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩).1
  have hτs : (τ : ℝ) < H.time j.succ := τ.2.2
  let t : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨τ, (H.toHistory.time_nonneg j.castSucc).trans (τ.2.1),
      hτs.le.trans (H.toHistory.time_le_horizon_at j.succ)⟩
  have hk : H.toHistory.activeStage t = j.castSucc := by
    apply le_antisymm _ (H.toHistory.le_activeStage t _ τ.2.1)
    by_contra hlt
    have hsucc : j.succ ≤ H.toHistory.activeStage t :=
      Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hlt)
    have := (H.time_strictMono.monotone hsucc).trans (H.toHistory.activeStage_time_le t)
    exact absurd (this.trans_lt hτs) (lt_irrefl _)
  have hmet : ∀ v, H.toHistory.stageMetric j.castSucc v =
      (H.toHistory.event j).incoming.flow.base.metric v :=
    fun v => ObservedHistory.stageMetric_castSucc_apply (H := H.toHistory) j v
  have hvol := H.toHistory.volume_ge_of_stage_window (κ := κ) t j.castSucc hk B.center hr
    hwin (by
      intro v hv x hx
      rw [hmet] at hx ⊢
      exact hB.2 v hv x hx)
    (fun q hq => hnc t q B.radius hτt hrρ hq)
  refine ⟨hκ, ?_⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim]
  rw [hmet] at hvol
  exact hvol

theorem isKappaNoncollapsed_of_terminalNoncollapsedBefore (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {κ ρ t₀ : ℝ} (hκ : 0 < κ) (hnc : H.TerminalNoncollapsedBefore hend G hG κ ρ t₀)
    (τ : (RealTimeInterval.closedOpen _ s G.lt).FlowTime) (B : Perelman.FlowMetricBall G.flow τ) :
    (τ : ℝ) ≤ t₀ → B.radius ≤ ρ → B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ := by
  intro hτt hrρ hB
  have hr := B.radius_pos
  have hwin : H.time (Fin.last H.eventCount) ≤ (τ : ℝ) - B.radius ^ 2 :=
    (hB.1 ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩).1
  have hT : H.time (Fin.last H.eventCount) < (τ : ℝ) := by
    have : 0 < B.radius ^ 2 := by positivity
    linarith
  have hτs : (τ : ℝ) < s := τ.2.2
  have hnc' := hnc τ hT hτs hτt
  set H' := H.extendHorizon τ (hend ▸ hT.le) (G.closedPrefix τ hT hτs) hG with hH'
  let t : Icc (0 : ℝ) H'.toHistory.horizon :=
    ⟨τ, (H.toHistory.time_nonneg _).trans hT.le, le_rfl⟩
  have hk : H'.toHistory.activeStage t = Fin.last H'.toHistory.eventCount :=
    le_antisymm (Fin.le_last _) (H'.toHistory.le_activeStage t _ hT.le)
  have hmet : ∀ v, H'.toHistory.stageMetric (Fin.last H'.toHistory.eventCount) v =
      G.flow.base.metric v :=
    fun v => ObservedHistory.stageMetric_last_of_lt (H := H'.toHistory) (h := hT) v
  have hvol := H'.toHistory.volume_ge_of_stage_window (κ := κ) t _ hk B.center hr
    hwin (by
      intro v hv x hx
      rw [hmet] at hx ⊢
      exact hB.2 v hv x hx)
    (fun q hq => hnc' t q B.radius le_rfl hrρ hq)
  refine ⟨hκ, ?_⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim]
  rw [hmet] at hvol
  exact hvol

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
