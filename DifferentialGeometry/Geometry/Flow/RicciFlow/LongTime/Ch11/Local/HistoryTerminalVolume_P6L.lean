import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryTerminalVolume

/-!
# L6-B 叶子：`HistoryTerminalVolume` 的 tested-volume 局部化（`_P6L`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2 (N)：
原 `ST/HistoryTerminalVolume.lean:280/355/408` 的 `htested : ∀ t … ∀ (q : stageAt carrier) ρ, …`
（carrier 全局）在证明里只于 `terminal_volume_ball_ge_of_tested_incomingFootprint`（`:280`）求值一次：
中心 `q` 满足 `HEq q p.val`（`isParabolicallyRmControlledBall_extendHorizon_of_incomingFootprint`
给出），`p` 是终端球心，时刻 `t ∈ 𝓝[<] s`，半径 `ρ ∈ (0, r)`。这里 `htested` 只要求
"`q` 与 `U` 中某点 `HEq`"，并加 `hpU : p.val ∈ U`。证明体照抄。
私有引理 `TerminalVolume:105`、`HistoryTerminalVolume:208/266` 一并复制（不 `open private`）。
**半径下界**（合同 §2 (N) 的核实项）：`:280` 经 `TerminalLimitMetric.volume_ball_ge_of_eventually_volume_ball_ge`
（`TerminalVolume:165`）对 `ρ ∈ (0, r)` 全取；该极限论证本身只需 `ρ ∈ 𝓝[<] r`，即 `ρ > r/2` 已够，
但 `r = a/√Q` 中的 `a` 是 Cone:108 内部取的小常数（依赖 `J`, `σ₀`），故不能由调用方给的固定窗口覆盖。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_P6L` 私有副本**：原 private `TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball`
（`TerminalVolume:105`），陈述与证明逐字。 -/
private theorem TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball_P6L
    (L : G.TerminalLimitMetric) (p : G.terminalRegularOpen) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p R)) :
    ∀ᶠ t in 𝓝[<] s,
      riemannianBallOf (G.flow.base.metric t) p.val ρ ⊆
        Subtype.val '' riemannianClosedBallOf L.metric p R := by
  let B : ℝ := R / ρ
  have hB : 1 < B := (lt_div_iff₀ hρ).mpr (by simpa only [one_mul] using hρR)
  have heps : 0 < B ^ 2 - 1 := by nlinarith
  obtain ⟨d, hd, hbound⟩ := L.exists_compact_quad_bound hcompact heps
  let F := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel
    G.terminalRegularOpen ⟨p⟩
  have hsource : riemannianClosedBallOf L.metric p R ⊆ F.source := subset_univ _
  filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
  have hlow : ∀ y ∈ riemannianClosedBallOf L.metric p R,
      ∀ v : TangentSpace ThreeModel y, L.metric.inner y v v ≤
        B ^ 2 * (G.flow.base.metric t).inner (F y)
          (mfderiv ThreeModel ThreeModel F y v) (mfderiv ThreeModel ThreeModel F y v) := by
    intro y hy v
    have hb := hbound t ht y hy v
    change L.metric.inner y v v ≤ (1 + (B ^ 2 - 1)) *
      (G.flow.base.metric t).inner y.val v v at hb
    have hdf : mfderiv ThreeModel ThreeModel F y v = v :=
      DifferentialGeometry.mfderiv_subtype_val_apply G.terminalRegularOpen y v
    rw [hdf]
    change L.metric.inner y v v ≤ B ^ 2 * (G.flow.base.metric t).inner y.val v v
    convert hb using 1
    ring
  have hcapture :=
    DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    L.metric (G.flow.base.metric t) F p (hρ.trans hρR) (zero_lt_one.trans hB) hcompact hsource hlow
  have hradius : R / B = ρ := by
    dsimp only [B]
    field_simp [ne_of_gt (hρ.trans hρR)]
  rw [hradius] at hcapture
  exact hcapture

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6L` 私有副本**：原 private
`RetainedCoreHistory.eventually_incomingFootprint_ball_subset_and_curvature_bound`
（`HistoryTerminalVolume:208`），陈述逐字；叶子换成 `…_P6L`。 -/
private theorem RetainedCoreHistory.eventually_incomingFootprint_ball_subset_and_curvature_bound_P6L
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (p : G.terminalRegularOpen) {r : ℝ} (c : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p r))
    (hfirst : H.time first ≤ c) (hroom : c ≤ s - r ^ 2)
    (U : Set (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K))
    (hcapture : riemannianBallOf L.metric p r ⊆
      H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K '' U)
    (hbound : ∀ v ∈ Ico c s, ∀ z ∈ U,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    ∀ᶠ t in 𝓝[<] s,
      H.horizon < t ∧ t < s ∧ H.time first ≤ t - ρ ^ 2 ∧
      riemannianBallOf (G.flow.base.metric t) p.val ρ ⊆
        (fun z => (H.toHistory.backwardSurvivorIncomingFootprintMap first
          (Fin.last H.eventCount) (Fin.le_last first) G K z).val) '' U ∧
      ∀ v ∈ Icc (t - ρ ^ 2) t, ∀ z ∈ U,
        ρ ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1 := by
  have hr : 0 < r := hρ.trans hρr
  obtain ⟨R, hρR, hRr⟩ := exists_between hρr
  have hclosedR : IsClosed (riemannianClosedBallOf L.metric p R) :=
    isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist L.metric p)
      continuous_const
  have hcompactR : IsCompact (riemannianClosedBallOf L.metric p R) :=
    hcompact.of_isClosed_subset hclosedR (riemannianClosedBallOf_mono L.metric p hRr.le)
  have htime : c + ρ ^ 2 < s := by
    have hsq : ρ ^ 2 < r ^ 2 := by nlinarith
    linarith
  filter_upwards [Ioo_mem_nhdsLT hs, Ioo_mem_nhdsLT htime,
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball_P6L
      L p hρ hρR hcompactR] with t ht htroom htball
  have hroom' : H.time first ≤ t - ρ ^ 2 := by linarith [htroom.1]
  refine ⟨ht.1, ht.2, hroom', ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := htball hx
    have hy' : y ∈ riemannianBallOf L.metric p r := by
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)
    obtain ⟨z, hz, hzy⟩ := hcapture hy'
    exact ⟨z, hz, congrArg Subtype.val hzy⟩
  · intro v hv z hz
    have hcv : c ≤ v := by linarith [htroom.1, hv.1]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ.le hρr.le 4)
      (normSq0S_nonneg _ _ _ _)).trans
        (hbound v ⟨hcv, hv.2.trans_lt ht.2⟩ z hz)

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_P6L` 私有副本**：原 private `volume_ball_eq_of_activeStage_eq`（`HistoryTerminalVolume:266`）。 -/
private theorem volume_ball_eq_of_activeStage_eq_P6L
    (A : ObservedHistory.{u}) (t : Icc (0 : ℝ) A.horizon)
    (last : Fin (A.eventCount + 1)) (hlast : A.activeStage t = last)
    (p : (A.stageAt t).Carrier) (q : (A.stage last).Carrier) (hpq : HEq p q) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel (A.stageAt t).Carrier
        (A.stageMetric (A.activeStage t) t)
        (riemannianBallOf (A.stageMetric (A.activeStage t) t) p r) =
      riemannianVolumeMeasure ThreeModel (A.stage last).Carrier
        (A.stageMetric last t) (riemannianBallOf (A.stageMetric last t) q r) := by
  subst last
  have hpq' : p = q := eq_of_heq hpq
  subst q
  rfl


/-- **`_P6L`**：原 `RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint`
（`HistoryTerminalVolume:280`）。改动：`htested` 只要求中心 `q` 与区域 `U` 中某点 `HEq`（时刻、半径
量词不变）；加 `hpU : p.val ∈ U`（唯一求值点 `HEq q p.val` 的成员关系来源）。原内部足迹集 `U` 改名 `W`。 -/
theorem RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint_P6L
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (p : G.terminalRegularOpen) (hpU : p.val ∈ U) {r κ σ : ℝ} (hr : 0 < r) (hrσ : r ≤ σ)
    (c : ℝ) (hcompact : IsCompact (riemannianClosedBallOf L.metric p r))
    (hfirst : H.time first ≤ c) (hroom : c ≤ s - r ^ 2)
    (W : Set (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K))
    (hcapture : riemannianBallOf L.metric p r ⊆
      H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K '' W)
    (hbound : ∀ v ∈ Ico c s, ∀ z ∈ W,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ z ∈ U, ∀ (q : (A.toHistory.stageAt time).Carrier), HEq q z →
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf
                (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric p r) := by
  apply L.volume_ball_ge_of_eventually_volume_ball_ge p hr hcompact
  intro ρ hρ hρr
  filter_upwards [H.eventually_incomingFootprint_ball_subset_and_curvature_bound_P6L G L hs first K
    gflow p c hcompact hfirst hroom W hcapture hbound hρ hρr] with t ht
  obtain ⟨ht, hts, hroomt, hballt, hboundt⟩ := ht
  let A := H.extendHorizon t ht.le
    (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit
  let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩
  obtain ⟨q, hqp, htest⟩ :=
    H.isParabolicallyRmControlledBall_extendHorizon_of_incomingFootprint G L hinit first K
      gflow hslabs hlast ht hts hρ hroomt p.val W hballt hboundt
  have hvol := htested t ht hts p.val hpU q hqp ρ hρ (hρr.le.trans hrσ) htest
  have hactive : A.toHistory.activeStage time = Fin.last H.eventCount :=
    A.toHistory.activeStage_at_horizon
  have hvolume := volume_ball_eq_of_activeStage_eq_P6L A.toHistory time (Fin.last H.eventCount)
    hactive q p.val hqp ρ
  have hmetric : A.toHistory.stageMetric (Fin.last H.eventCount) t = G.flow.base.metric t :=
    A.toHistory.stageMetric_last_of_lt (h := H.time_le_horizon.trans_lt ht) t
  change ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
    riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
      (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
      (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ) at hvol
  rw [hvolume] at hvol
  change ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
    riemannianVolumeMeasure ThreeModel (A.toHistory.stage (Fin.last H.eventCount)).Carrier
      (A.toHistory.stageMetric (Fin.last H.eventCount) t)
      (riemannianBallOf (A.toHistory.stageMetric (Fin.last H.eventCount) t) p.val ρ) at hvol
  rwa [hmetric] at hvol

/-- **`_P6L`**：原 `RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball`
（`HistoryTerminalVolume:355`）。改动：`htested` 限于 `U`（`HEq` 形），加 `hpU : p.val ∈ U`。 -/
theorem RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball_P6L
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    {c : ℝ} (hfirst : H.time first ≤ c) (hcs : c ≤ s)
    (S : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K) (RealTimeInterval.closed c s hcs))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      S.base.metric v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (p : G.terminalRegularOpen) (hpU : p.val ∈ U)
    (B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p B.radius))
    (himage : H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
      (Fin.le_last first) G K '' B.set = riemannianBallOf L.metric p B.radius)
    {κ σ : ℝ} (hrσ : B.radius ≤ σ)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ z ∈ U, ∀ (q : (A.toHistory.stageAt time).Carrier), HEq q z →
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf
                (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal B.radius ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric p B.radius) := by
  have hstart : c ≤ s - B.radius ^ 2 :=
    (hB.1 ⟨le_rfl, sub_le_self s (sq_nonneg B.radius)⟩).1
  apply H.terminal_volume_ball_ge_of_tested_incomingFootprint_P6L G L hinit hs first K
    S.base.metric hslabs hlast U p hpU B.radius_pos hrσ (s - B.radius ^ 2) hcompact
    (hfirst.trans hstart) le_rfl B.set himage.ge
  · intro v hv z hz
    exact hB.2 v ⟨hv.1, hv.2.le⟩ z hz
  · exact htested

/-- **`_P6L`**：原
`RetainedCoreHistory.normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball`
（`HistoryTerminalVolume:408`）。改动：`htested` 限于 `U`（`HEq` 形），加 `hpU : p.val ∈ U`
（调用方 Cone:108 由 `p ∈ B(x, r) ⊆ B(x, ρ) ⊆ U` 给出）。 -/
theorem RetainedCoreHistory.normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball_P6L
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    {c : ℝ} (hfirst : H.time first ≤ c) (hcs : c ≤ s)
    (S : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K) (RealTimeInterval.closed c s hcs))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      S.base.metric v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    (x p : G.terminalRegularOpen) (hpU : p.val ∈ U)
    {Q r a R : ℝ} (hQ : 0 < Q) (hr : 0 ≤ r) (hra : r + a ≤ R)
    (B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled)
    (hradius : B.radius = a / Real.sqrt Q)
    (hcompact : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ L.metric) x R))
    (hp : p ∈ riemannianClosedBallOf (scaleMetric Q hQ L.metric) x r)
    (himage : H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
      (Fin.le_last first) G K '' B.set = riemannianBallOf L.metric p B.radius)
    {κ σ : ℝ} (hrσ : B.radius ≤ σ)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ z ∈ U, ∀ (q : (A.toHistory.stageAt time).Carrier), HEq q z →
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf
                (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal (κ * a ^ 3) ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen (scaleMetric Q hQ L.metric)
        (riemannianBallOf (scaleMetric Q hQ L.metric) p a) := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hscale : Real.sqrt Q * B.radius = a := by
    rw [hradius]
    field_simp
  have ha : 0 < a := hscale ▸ mul_pos hsqrt B.radius_pos
  have hsmall : IsCompact
      (riemannianClosedBallOf (scaleMetric Q hQ L.metric) p a) :=
    hcompact.of_isClosed_subset
      (isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
        (scaleMetric Q hQ L.metric) p) continuous_const)
      (riemannianClosedBallOf_subset_of_add_radius_le (scaleMetric Q hQ L.metric)
        hr ha.le hra hp)
  have hphysical : IsCompact (riemannianClosedBallOf L.metric p B.radius) := by
    rw [← riemannianClosedBallOf_scaleMetric Q hQ, hscale]
    exact hsmall
  have hv := H.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball_P6L G L hinit hs
    first K hfirst hcs S hslabs hlast U p hpU B hB hphysical himage hrσ htested
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled :=
    (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
      L.metric Q hQ p B.radius (ENNReal.ofReal κ)).mpr (by simpa only [hdim] using hv)
  rw [hscale, hdim] at hscaled
  simpa only [ENNReal.ofReal_mul' (pow_nonneg ha.le 3), ENNReal.ofReal_pow ha.le] using hscaled

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
