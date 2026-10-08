import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorKappaP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PK

/-!
# 切片 BCBD 的 U 局部供给：κ 项（O-CH11-SLICE-BCBD G1，后缀 `_P6SB`）

R-C11-20 D-20-7 / D-20-17：验收终点形 = SLTPROD G3d `hanchor0_eventSlab_star_firstExit_P6SP` 的结论逐字
（`∀ A > 0, ∃ Q ≥ 2, ∀ᶠ n, ∀ z ∈ B_t(yG, A/√R), R(t, z) ≤ Q·R(t, yG)`）。那条链的 kernel
（`RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2`）对 κ 只消费**当前 slab 内**、`U = B_t(yG, Rad/√R)`
上的点（`hnc` 槽，经 `hnc_window_of_tracedKappa_P6M` → `tested_kappa_window_of_tracedKappa_P6M`，后者只在
`activeStage τ = activeStage σ` 处调用 trace-κ）。G3d 的前提 `hvolK` 却要求从 `B_σ(y, D/√R)` 出发、深度 `B/R`
的**任意** trace（可跨 event）——比 kernel 实际用到的强。

本文件只用既有选点资料 + FRESH 原尺度 κ（`KappaSeedWindowFwd_C11PK`，PBKAPPA 登记）+ 选点 gate + 同 stage
`hdistW`，**PROVED** 地给出 kernel 的 `hnc` 槽：
* `tested_kappa_window_sameStage_P6SB` / `hnc_window_sameStage_P6SB`：`_P6M` 两引理的同 stage 孪生（trace-κ
  前提只在 `activeStage v = activeStage σ` 时要求；证明体逐字，只多传一个 stage 等式）。
* `hkappaS_of_fresh_P6SB`：同 stage trace-κ ⇐ FRESH + `hdistW`（同 stage 距离）+ gate
  `d_σ(O, y) + (L+1)/√R ≤ Aκ·r` + 时间窗 `Tn − r²/2 ≤ σ − T/R`；尺度上限 `ρnc := r/200`（`< r/100`）。
* **`hnc_window_of_fresh_P6SB`**：kernel `hnc` 槽逐字 + `hρ`（`r/200·√R → ∞`）⇐ 上述。
不用 hTR / TimeCore / 切片 BCBD / capped κ 的 traced-region 前提：footprint 只靠同 stage `hdistW` + gate。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- 首末 stage 指标相等时的单点 trace（`_P6M` 私有引理的公开孪生）。 -/
theorem exists_trace_of_stage_eq_P6SB (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- 球成员：incoming slab 度量 ↔ `stageMetric m`（`_P6M` 私有引理的公开孪生）。 -/
theorem mem_ball_incoming_P6SB (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
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

/-- slab 内部时刻的 `activeStage`（`_P6M` 私有引理的公开孪生）。 -/
theorem activeStage_eq_of_mem_slab_P6SB (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- **同 stage 孪生（`_P6SB`）**：`tested_kappa_window_of_tracedKappa_P6M` 的 trace-κ 前提只在
`activeStage v = activeStage σ` 时要求；结论逐字。 -/
theorem tested_kappa_window_sameStage_P6SB (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {t : ℝ} (hjt : K.time j.castSucc < t) (htj : t < K.time j.succ)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = t)
    (y : (K.toHistory.stageAt σ).Carrier) (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG)
    {κ ρ Rad θ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - θ ≤ v →
      K.toHistory.activeStage v = K.toHistory.activeStage σ →
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
    K.activeStage_eq_of_mem_slab_P6SB j σ (by rw [hσ]; exact hjt.le) (by rw [hσ]; exact htj)
  have hτact : K.toHistory.activeStage τ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6SB j τ hjτ.le (hτt.trans_lt htj)
  have hvt : τ ≤ σ := show (τ : ℝ) ≤ σ by rw [hσ]; exact hτt
  let x : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hσact.symm) z
  have hxz : HEq x z := cast_heq _ _
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad :=
    mem_ball_incoming_P6SB K j hσact.symm σ Rad z yG x y hxz hyG (by rw [hσ]; exact hz)
  obtain ⟨tr, htr⟩ := exists_trace_of_stage_eq_P6SB K.toHistory (hτact.trans hσact.symm)
    (K.toHistory.activeStage_mono hvt) x
  have hθ' : (σ : ℝ) - θ ≤ τ := by rw [hσ]; exact haτ
  have hpt : tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt) = zz :=
    eq_of_heq (htr.trans (hxz.trans hzz.symm))
  have hball' : K.toHistory.isParabolicallyRmControlledBall τ
      (tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt)) b := by
    rw [hpt]
    exact hball
  have h := hK x hx τ hvt hθ' (hτact.trans hσact.symm) tr b hb hbρ hball'
  rw [hpt, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **同 stage 孪生（`_P6SB`）**：`hnc_window_of_tracedKappa_P6M` 的 `hkappa` 只在
`activeStage v = activeStage σ` 时要求；结论 = kernel 窗口 `hnc` 逐字。 -/
theorem hnc_window_sameStage_P6SB {K : ℕ → RetainedCoreHistory.{u}}
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
      (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
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
  have hsingle := (K n).tested_kappa_window_sameStage_P6SB (j n) (hjt n) (htj n) (σ n) (hσ n)
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


namespace ObservedHistory

/-- **同 stage trace-κ ⇐ FRESH（`_P6SB`，PROVED）**：原尺度 FRESH（`KappaSeedWindowFwd_C11PK`，seed
`(Tn, pT, r)`）+ 同 stage `hdistW`（trace 点到 seed trace 点的距离 `≤ d_σ(O, y) + L/√R`）+ gate
`d_σ(O, y) + (L+1)/√R ≤ Aκ·r`（严格进 FRESH footprint）+ 时间窗 `Tn − r²/2 ≤ σ − T/R` ⇒ 从 `B_σ(y, D/√R)`
出发、同 stage、深度 `≤ T/R` 的 trace 点在尺度 `≤ r/200` 上 κ-noncollapsed。 -/
theorem hkappaS_of_fresh_P6SB {H : ℕ → ObservedHistory.{u}}
    {nr : ℝ → ℝ} {Aκ κ Tκ r : ℝ}
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (H n))
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (H n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((H n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (Tn n)) ((H n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((H n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (H n) (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((H n).stageMetric
      ((H n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
            ((H n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (H n).activeStage v = (H n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (σ n))
          ((H n).activeStage_mono hvs) x,
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage v) v)
            ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
              ((H n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
                ((H n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (H n).activeStage v = (H n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
        ((H n).activeStage (σ n)) ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r / 200 →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  intro D T hD hT
  filter_upwards [hdistW D T hD hT, hwinF T hT, hgate, hL.eventually_ge_atTop 0] with
    n hdW hwin hg hL0
  intro x hx v hvt hvT hst tr r'' hr'' hr''le hball
  have hTv : (Tn n : ℝ) - r ^ 2 / 2 ≤ v := hwin.trans hvT
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    rw [hclock n]
    have : 0 ≤ r ^ 2 := sq_nonneg r
    linarith
  have hvTn : v ≤ Tn n := hvt.trans (hsT n)
  have hd := hdW x hx v hav hvt hvT hst tr
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hRpos n)
  have hlt : ENNReal.ofReal (L n / Real.sqrt (R n)) <
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hsR)]
    exact div_lt_div_of_pos_right (by linarith) hsR
  have hne : riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
        ((H n).activeStage_mono (hsT n))) (y n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hg)
  have hmem : tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt) ∈
      riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v)
        ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
          ((H n).activeStage_mono hvTn)) (Aκ * r) :=
    lt_of_le_of_lt hd ((ENNReal.add_lt_add_left hne hlt).trans_le hg)
  exact hWK n (Tn n) (pT n) r (hTκ n) (htimeS n) (hsmallS n) (hvolS n) (hnrS n) (aSeed n)
    (haT n) (hclock n) (seedTrace n) v hav hvTn hTv _ hmem r'' hr''.le (by linarith) hball

/-- **kernel `hnc` 槽 ⇐ FRESH（`_P6SB`，PROVED）**：`RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2`
（WBADAPT）/ SLTLOCAL anchor kernel 的 `hnc` + `hρ` 两槽，`ρ := r/200`，只用 FRESH seed 数据 + gate +
同 stage `hdistW` + 时间窗；替代 G3d 前提 `hvolK`（跨 event 全 trace 形）在 anchor 中的唯一用途。 -/
theorem hnc_window_of_fresh_P6SB {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {nr : ℝ → ℝ} {Aκ κ Tκ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (K n).toHistory)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    Tendsto (fun n => r / 200 *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop ∧
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
        ∀ (b : ℝ), 0 < b → b ≤ r / 200 →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  refine ⟨?_, ?_⟩
  · have hs : Tendsto (fun n => Real.sqrt (R n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hRlim
    refine (hs.const_mul_atTop (by positivity : (0 : ℝ) < r / 200)).congr fun n => ?_
    rw [hRn n]
  · exact hnc_window_sameStage_P6SB hjt htj σ hσ y yG hyG R hRpos hRn hκ (fun _ => r / 200)
      (hkappaS_of_fresh_P6SB hWK Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hTκ
        htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistW)

end ObservedHistory

/-- consumer：同 stage 孪生比 `_P6M` 原形更弱（原 trace-κ 前提直接限制到同 stage）。 -/
example : type_of% @ObservedHistory.hnc_window_of_tracedKappa_P6M.{u} := by
  intro K j t hjt htj σ hσ y yG hyG R hR hRn κ hκ ρnc hkappa
  exact ObservedHistory.hnc_window_sameStage_P6SB hjt htj σ hσ y yG hyG R hR hRn hκ ρnc
    (fun D T hD hT => (hkappa D T hD hT).mono fun _ hn x hx v hvt hvT _ => hn x hx v hvt hvT)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
