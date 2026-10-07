import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeP6M

/-!
# 窗口 `hnc` ⇐ K 层 trace-local κ（O-CH11-P6ANCH G1w 续，后缀 `_P6M`）

SLT 窗口版（G1w `hanchor0_of_closure_data_window_P6M`）的 `hnc` 只要窗口 `[t − B/R, t]` 内、球
`B_G(y, Rad/√R)` 中心的 tested κ。本文件把它从 K 层 trace-local κ（P6D G2 / G5c 的 `hkappa` 形；
`Pre841` 经 G0 `exists_tracedKappa_of_kseq_P6D2` 给出，`ρ = ρnc`）推出：
* 窗口时刻 `τ` 与基点时刻 `σ = t` 同在 event slab `j` 内 ⇒ `activeStage τ = activeStage σ = j.castSucc`，
  `τ → σ` 的 backward trace 是单点 trace（`exists_trace_of_stage_eq_P6M`），trace 点 = 中心本身；
* K 层 `stageMetric j.castSucc` 与 incoming slab 度量识别（`stageMetric_castSucc_apply`）给球成员；
* 再经 G3 桥 `tested_noncollapse_eventPrefix_P6M`（`a := t − B/R`）得 SLT 的 `hnc` 逐字形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- 首末 stage 指标相等时的单点 trace（trace 点 `HEq` 端点）。 -/
private theorem exists_trace_of_stage_eq_P6M (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- 球成员：incoming slab 度量 ↔ `stageMetric m`（`m = j.castSucc`，`HEq` 搬运）。 -/
private theorem mem_ball_incoming_P6M (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v r : ℝ)
    (z yG : (K.stage j.castSucc).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG)
    (h : z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) yG r) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r := by
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_castSucc_apply]
  exact h

/-- slab 内部时刻的 `activeStage`。 -/
private theorem activeStage_eq_of_mem_slab_P6M (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- **`_P6M`（单 history）**：K 层 trace-local κ（基点 `(σ, y)`、半径 `Rad`、深度 `θ`、`r'' ≤ ρ`）⇒
G3 桥 `tested_noncollapse_eventPrefix_P6M` 所需的 K 层窗口 tested κ（`U = B_G(t)(yG, Rad)`、
`a = t − θ`）。 -/
theorem tested_kappa_window_of_tracedKappa_P6M (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {t : ℝ} (hjt : K.time j.castSucc < t) (htj : t < K.time j.succ)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = t)
    (y : (K.toHistory.stageAt σ).Carrier) (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG)
    {κ ρ Rad θ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρ →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), t - θ ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) yG Rad,
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b) := by
  intro τ haτ hτt hjτ _ z hz zz hzz b hb hbρ hball
  have hσact : K.toHistory.activeStage σ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6M j σ (by rw [hσ]; exact hjt.le) (by rw [hσ]; exact htj)
  have hτact : K.toHistory.activeStage τ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6M j τ hjτ.le (hτt.trans_lt htj)
  have hvt : τ ≤ σ := show (τ : ℝ) ≤ σ by rw [hσ]; exact hτt
  let x : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hσact.symm) z
  have hxz : HEq x z := cast_heq _ _
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad :=
    mem_ball_incoming_P6M K j hσact.symm σ Rad z yG x y hxz hyG (by rw [hσ]; exact hz)
  obtain ⟨tr, htr⟩ := exists_trace_of_stage_eq_P6M K.toHistory (hτact.trans hσact.symm)
    (K.toHistory.activeStage_mono hvt) x
  have hθ' : (σ : ℝ) - θ ≤ τ := by rw [hσ]; exact haτ
  have hpt : tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt) = zz :=
    eq_of_heq (htr.trans (hxz.trans hzz.symm))
  have hball' : K.toHistory.isParabolicallyRmControlledBall τ
      (tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt)) b := by
    rw [hpt]
    exact hball
  have h := hK x hx τ hvt hθ' tr b hb hbρ hball'
  rw [hpt, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **`_P6M`（序列 `hnc`，窗口形）**：K 层 trace-local κ（P6D G2 / G5c 的 `hkappa`，`ρnc`）⇒ G1w
`hanchor0_of_closure_data_window_P6M` 的窗口 `hnc`（`H n := (K n).prefixAt (j n).castSucc`、
`G n := ((K n).toHistory.event (j n)).incoming`、`ρ := ρnc`）。 -/
theorem hnc_window_of_tracedKappa_P6M {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (j n).castSucc).time
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) < T)
      (hTs : T < (K n).time (j n).succ), T ≤ t n →
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (j n).castSucc).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          (((K n).toHistory.event (j n)).incoming.closedPrefix T hT hTs) ((K n).event_initial (j n))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (j n).castSucc).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
              (yG n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  intro Rad B
  filter_upwards [hkappa (max Rad 1) (max B 1) (by positivity) (by positivity)] with n hn
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hsingle := (K n).tested_kappa_window_of_tracedKappa_P6M (j n) (hjt n) (htj n) (σ n) (hσ n)
    (y n) (yG n) (hyG n) (Rad := max Rad 1 / Real.sqrt (R n)) (θ := max B 1 / R n) hκ.le hn
  have hU : ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
      (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
        (max Rad 1 / Real.sqrt (R n)) := by
    intro z hz
    rw [← hRn n] at hz
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hz
  have hbridge := (K n).tested_noncollapse_eventPrefix_P6M (j n) (a := t n - max B 1 / R n)
    (t := t n) (ρ := ρnc n)
    (riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
    (fun τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hball =>
      hsingle τ haτ hτt hjτ hτj z (hU z hz) zz hzz b hb hbρ hball) ((K n).prefixAt_time_last _)
  intro T hT hTs hTt hBT
  refine hbridge T hT hTs hTt ?_
  rw [← hRn n] at hBT
  have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
