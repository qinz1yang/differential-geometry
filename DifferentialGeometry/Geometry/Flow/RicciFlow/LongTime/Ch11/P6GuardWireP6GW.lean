import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFifthP6AN5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedCone3C11KX
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowSeedBaseC11WB

/-!
# GUARDWIRE G1：ANCHOR top 消费链改接 guarded ShortSLT（O-CH11-GUARDWIRE，后缀 `_P6GW`）

KSWEXIT 交付 `shortSLT_guarded_C11KX : 0 < θ → ShortSLTGuarded_C11KX θ`（无 binder）：ShortSLT 的 U 侧数据只在
逐点 guard `GuardKX_C11KX (R(t, ·)) q Ctime t v z`（`2·Ctime·max(R(t, z), q)·(t − v) ≤ 1`）上要求。本文件把
ANCHOR3/4/5 的 top-anchor 消费链改接到 guarded 合同，目标 = **hseedTop 消去**（event 构形；final 见 G2 文件）。

**用点对照（AN2 `TopAnchorInputs` 的 ShortSLT 字段 → 来源）**：
* `hW`（top witness）：hgood 空间分量 + 三角不等式（AN3 `pickedBallWitness_top_of_hgood_P6AN3`），不变、无 guard。
* `hslabs`（prefix event slabs，**跨 slab**）：`hslabSel : EventSlabsDerivative Ctime (Cg·R)`（J10 残余），经
  `hderE_of_slabSel_P6AN5`；**不经 U 侧 WindowSeed** ⇒ guard 直接丢弃（透传）。⇒ KSWEXIT 剩余 (2)
  「跨 slab hslabs 来源」关闭：不需要 trace 版 point-anchor。guarded 改接**不改变** `hslabSel` 的阈值形
  （`Q ≤ Cg·R`），J10 残余仍由 SLTLOCAL（SLT 核孪生）负责。
* `hder`（top slab 时间导数）/ `hgrad`（top slab 梯度）：原 ⇐ hgood + **hseedTop**；现 ⇐ hgood + guarded seed
  `PickedBallWindowSeedGuarded_P6GW`（只在 guard 点），后者由 WSBASE
`ObservedHistory.windowSeed_pointAnchor_C11WB`
  逐点付（`pickedBallWindowSeedGuarded_top_P6GW` / `hseedTopGuarded_seq_P6GW`，PROVED 无 binder）：anchor
`(σ, x)`、
  `M := max(R(t, x), Cg·R_n)`、`q := M/Cg`、`Λ := Cg`、`θ := 1/(2·Ct·Cg)`；guard 深度 `1/(2·Ct·M)` =
`θ/q`。
* `hnc`（κ）：`hkappa`（`pickedBallKappa_top_seq_of_hkappa_P6AN3`），不经 hseedTop ⇒ guard 丢弃（透传）。
* ShortSLT binder：`shortSLT_C11KS2` →
`shortSLT_guarded_C11KX`（`hanchor0_{event,final}_of_topInputsGuarded_P6GW`）。

**主定理**：`topAnchorInputs_guarded_P6GW`（ANCHOR5 `topAnchorInputs_of_hgood_local_noJ10_P6AN5` 的孪生；
binder 表 = AN5 表 − hseedTop + {`0 ≤ C2`、K0 `hsmall / hclock / hRr`、`hpin`}——后四项本就在 AN5 全链里，
故全链净新增只有 `0 ≤ C2`）。guard 常数取 `Ctime + Ctg + 1`（> 0，≥ Ctg）。
非循环：无 hseedTop / hpick / `PickedBallTop_C11PB` / `hdistW` 槽 / `hanchor0` 前提（审计 deny 扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section Contracts

/-- **guarded window seed（`_P6GW`）**：`PickedBallWindowSeed_C11PB` 逐字，每个求值点 `(v′, x)` 加 KSWEXIT
guard `GuardKX_C11KX (R(v, ·)) qthr Ct v v′ x`（`2·Ct·max(R(v, x), qthr)·(v − v′) ≤ 1`；top 时刻 = `v`）。
= ANCHOR 链 hseedTop 的 guarded 替代物（在 top 点 `v := t n`、`w := yG n`），由 WSBASE point-anchor 付
（`pickedBallWindowSeedGuarded_top_P6GW`）。 -/
def PickedBallWindowSeedGuarded_P6GW (β Rad qthr : ℝ) (Ct : ℝ≥0) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier)
    (O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time j.castSucc) v,
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
    qthr < (K.toHistory.event j).incoming.flow.scalar v' x →
    GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) qthr Ct v v' x →
    riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v') O x ≤ D

/-- **guarded hgrad（`_P6GW`）**：`PickedBallGrad_C11PB` 逐字 + 同一 guard（= ShortSLTGuarded 的 `hgrad`）。 -/
def PickedBallGradGuarded_P6GW (β Rad qthr : ℝ) (Ct Cgrad : ℝ≥0) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time j.castSucc) v,
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
    qthr < (K.toHistory.event j).incoming.flow.scalar v' x →
    GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) qthr Ct v v' x →
    ∀ ξ : TangentSpace ThreeModel x,
      |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
        Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
          Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
          Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)

/-- **guarded hκ（`_P6GW`）**：`PickedBallKappa_C11PB` 逐字，测试点 `(τ, z)` 加 guard
`GuardKX_C11KX (R(v, ·)) qthr Ct v τ z`（= ShortSLTGuarded 的 `hnc`，WSBASE G3 §3 五要素 4）。 -/
def PickedBallKappaGuarded_P6GW (β Rad ρ κ qthr : ℝ) (Ct : ℝ≥0) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
    K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
    ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) qthr Ct v τ z →
    ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
    ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
          (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
          (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)

/-- **inhabitant / 弱化（`_P6GW`，PROVED）**：未 guard 的 window seed ⇒ guarded（丢 guard）。 -/
theorem PickedBallWindowSeed_C11PB.guarded_P6GW {β Rad qthr : ℝ} (Ct : ℝ≥0)
    {K : RetainedCoreHistory.{u}} {j : Fin K.eventCount} {v : ℝ}
    {w O : (K.stage j.castSucc).Carrier} {D : ℝ≥0∞}
    (h : PickedBallWindowSeed_C11PB β Rad qthr K j v w O D) :
    PickedBallWindowSeedGuarded_P6GW β Rad qthr Ct K j v w O D :=
  fun x hx v' hv' hw hq _ => h x hx v' hv' hw hq

/-- **inhabitant / 弱化（`_P6GW`，PROVED）**：未 guard 的 hgrad ⇒ guarded。 -/
theorem PickedBallGrad_C11PB.guarded_P6GW {β Rad qthr : ℝ} (Ct : ℝ≥0) {Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {j : Fin K.eventCount} {v : ℝ}
    {w : (K.stage j.castSucc).Carrier}
    (h : PickedBallGrad_C11PB β Rad qthr Cgrad K j v w) :
    PickedBallGradGuarded_P6GW β Rad qthr Ct Cgrad K j v w :=
  fun x hx v' hv' hw hq _ ξ => h x hx v' hv' hw hq ξ

/-- **`pickedBallKappa_guarded_P6GW`（`_P6GW`，PROVED）**：`PickedBallKappa_C11PB` ⇒ guarded 形（丢 guard）。
ANCHOR top 链的 κ 来源 `hkappa`（`pickedBallKappa_top_seq_of_hkappa_P6AN3`）**不经 hseedTop**，故 guarded
改接只需这一步弱化；guard 集上的独立来源（PICKSEL footprint 去 `hRic`）见 G3。 -/
theorem pickedBallKappa_guarded_P6GW {β Rad ρ κ qthr : ℝ} (Ct : ℝ≥0)
    {K : RetainedCoreHistory.{u}} {j : Fin K.eventCount} {v : ℝ}
    {w : (K.stage j.castSucc).Carrier}
    (h : PickedBallKappa_C11PB β Rad ρ κ K j v w) :
    PickedBallKappaGuarded_P6GW β Rad ρ κ qthr Ct K j v w :=
  fun τ h1 h2 h3 h4 z hz _ zz hzz b hb hbρ hc => h τ h1 h2 h3 h4 z hz zz hzz b hb hbρ hc

/-- **inhabitant（`_P6GW`）**：`Rad = 0` 时球空，guarded window seed 平凡成立。 -/
theorem pickedBallWindowSeedGuarded_zero_P6GW (β qthr : ℝ) (Ct : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) (v : ℝ)
    (w O : (K.stage j.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedBallWindowSeedGuarded_P6GW β 0 qthr Ct K j v w O D :=
  (pickedBallWindowSeed_zero_C11PB β qthr K j v w O D).guarded_P6GW Ct

/-- **guarded top-anchor 合同 `TopAnchorInputsGuarded_P6GW β`（`_P6GW`，合同
Prop）**：`TopAnchorInputs_P6AN2 β` 逐字，
只把 ShortSLT U 侧四项 `hslabs / hder / hgrad / hnc` 的求值点加 KSWEXIT guard
`GuardKX_C11KX (R(t, ·)) q Ctime t v z`（与 `ShortSLTGuarded_C11KX` 同形、同序）。旧合同 ⇒ 新合同
（`TopAnchorInputs_P6AN2.toGuarded_P6GW`，丢 guard）。 -/
def TopAnchorInputsGuarded_P6GW (β : ℝ) (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (t : ℕ → ℝ) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier) : Prop :=
  ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧ ∃ (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ),
  Perelman.AdmissiblePinchingFunction phi ∧ ∃ Cq : ℝ,
  ∀ A : ℝ, 0 < A → ∀ Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Λ → StandardCap.transitionEnd < Dcap →
  Dcap ≤ Rrad → 0 < ζ₀ → ∃ Qcap : ℝ, ∀ᶠ n in atTop,
  ∃ q ρ : ℝ, 0 < q ∧ q ≤ Cq * (G n).flow.scalar (t n) (y n) ∧
    Λ ≤ (G n).flow.scalar (t n) (y n) ∧ Λ ≤ (G n).flow.scalar (t n) (y n) * t n ∧
    ∃ (p : CutoffParameters) (T₀ : ℝ), T₀ ≤ t n - β / (G n).flow.scalar (t n) (y n) ∧
    ∃ records : (∀ i : Fin (H n).eventCount, T₀ ≤ (H n).time i.succ →
        GeometricCutoffRecord (H n).toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) ∧
      Rrad ≤ p.modelRadius ∧ 2 ≤ p.modelOrder ∧ p.modelAccuracy ≤ ζ₀ ∧
      ∃ U : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
        (∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < (G n).flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
            W.capTubeHasNeckChart ε) ∧
        (∀ j : Fin (H n).eventCount,
          ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v z →
          |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
            Ctime * (G n).flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential (G n).flow v x w| ≤
              Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
                Real.sqrt (((G n).flow.base.metric v).inner x w w)) ∧
        (∀ j : Fin (H n).eventCount,
          Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
            (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
              Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi ∧
        (∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
          t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
          let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) T z →
          ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n)) ∧
      ((∃ (j : Fin (H n).eventCount) (hT : T₀ ≤ (H n).time j.succ)
          (hl : j.succ ≤ Fin.last (H n).eventCount)
          (B : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
          (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t n - (H n).time j.succ ≤ β * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          (G n).flow.scalar (t n) z ≤ Qcap * (G n).flow.scalar (t n) (y n))

/-- **旧合同 ⇒ guarded 合同（`_P6GW`，PROVED，inhabitant 级）**：`TopAnchorInputs_P6AN2 β` 丢 guard 即得
`TopAnchorInputsGuarded_P6GW β`（guarded 合同更弱）。 -/
theorem TopAnchorInputs_P6AN2.toGuarded_P6GW {β : ℝ} {s t : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (h : TopAnchorInputs_P6AN2 β H hend s G hGi t y) :
    TopAnchorInputsGuarded_P6GW β H hend s G hGi t y := by
  obtain ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, h⟩ := h
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq,
    fun A hA Λ Dcap Rrad ζ₀ Rad hΛ hD1 hD2 hζ => ?_⟩
  obtain ⟨Qcap, hcap⟩ := h A hA Λ Dcap Rrad ζ₀ Rad hΛ hD1 hD2 hζ
  refine ⟨Qcap, hcap.mono fun n hn => ?_⟩
  obtain ⟨q, ρ, hq, hqC, hΛR, hΛRt, p, T₀, hT₀, records, hcan, hRrad, hord, hacc, U, hU, hwit,
    hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ, hcmp⟩ := hn
  refine ⟨q, ρ, hq, hqC, hΛR, hΛRt, p, T₀, hT₀, records, hcan, hRrad, hord, hacc, U, hU, hwit,
    fun i first hf z hz B v hv hav hqv _ => hderE i first hf z hz B v hv hav hqv,
    fun x hx v hv hav hqv _ => hderT x hx v hv hav hqv,
    fun x hx v hv hav hqv _ => hgrad x hx v hv hav hqv, hpinE, hpinT, ?_, hΛρ, hcmp⟩
  intro T hT hTs hTt haT _ _ z hz _
  exact hkap T hT hTs hTt haT z hz

/-- **`hanchor0_of_shortSLTGuarded_top_P6GW`（`_P6GW`，PROVISIONAL：binder = `ShortSLTGuarded_C11KX
β` +
`TopAnchorInputsGuarded_P6GW β`）**：AN2 `hanchor0_of_shortSLT_top_P6AN2` 逐字，合同换 guarded 形；
证明体逐字（ShortSLTGuarded 的参数顺序与旧合同相同，只是 U 侧四项多一个 guard 前提）。 -/
theorem hanchor0_of_shortSLTGuarded_top_P6GW {β : ℝ} (hX : ShortSLTGuarded_C11KX.{u} β)
    {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hin : TopAnchorInputsGuarded_P6GW β H hend s G hGi t y) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n) := by
  obtain ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, hin⟩ := hin
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, -, hΛ, hD1, hD2, hζ, hX'⟩ :=
    hX hε κ C1 C2 hκ Ctime Cgrad hphi A hA Cq
  obtain ⟨Qcap, hcap⟩ := hin A hA Λ Dcap Rrad ζ₀ Rad hΛ hD1 hD2 hζ
  refine ⟨max (max Q Qcap) 2, le_max_right _ _, ?_⟩
  filter_upwards [hcap] with n hn
  obtain ⟨q, ρ, hq, hqC, hΛR, hΛRt, p, T₀, hT₀, records, hcan, hRrad, hord, hacc, U, hU, hwit,
    hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ, hcmp⟩ := hn
  have hR0 : 0 ≤ (G n).flow.scalar (t n) (y n) := by linarith
  intro z hz
  have hb1 := fun hc => (hcmp hc z hz).trans
    (mul_le_mul_of_nonneg_right ((le_max_right Q Qcap).trans (le_max_left _ 2)) hR0)
  have hb2 := fun hc => (hX' (H n) (hend n) (G n) (hGi n) (hat n) (hts n) (y n) q ρ hq hqC hΛR
    hΛRt T₀ hT₀ records hcan hRrad hord hacc U hU hwit hderE hderT hgrad hpinE hpinT hkap hΛρ hc z
    hz).trans (mul_le_mul_of_nonneg_right ((le_max_left Q Qcap).trans (le_max_left _ 2)) hR0)
  exact (Classical.em _).elim hb1 hb2

/-- **final 构形（`_P6GW`，PROVISIONAL：binder = `TopAnchorInputsGuarded_P6GW β` 单项）**：AN2 / KSW2
`hanchor0_final_of_topInputs_P6AN2` 的 guarded 孪生；`ShortSLTGuarded_C11KX β` 由 KSWEXIT
`shortSLT_guarded_C11KX hβ`（无 binder）付。结论逐字。 -/
theorem hanchor0_final_of_topInputsGuarded_P6GW {β : ℝ} (hβ : 0 < β)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hin : TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
          (A / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
        (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) z ≤
          Q * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) :=
  hanchor0_of_shortSLTGuarded_top_P6GW (shortSLT_guarded_C11KX hβ)
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    (s := fun n => (K n).horizon) (y := yG) (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) htl htK hin

/-- **event 构形（`_P6GW`，PROVISIONAL：binder = `TopAnchorInputsGuarded_P6GW β` 单项）**：KSW2
`hanchor0_event_of_topInputs_P6AN2` 的 guarded 孪生（ShortSLT 侧由 `shortSLT_guarded_C11KX` 付）。 -/
theorem hanchor0_event_of_topInputsGuarded_P6GW {β : ℝ} (hβ : 0 < β)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hin : TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
  hanchor0_of_shortSLTGuarded_top_P6GW (shortSLT_guarded_C11KX hβ)
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    hin

end Contracts

section Producers

/-- **G1 `pickedBallGrad_guarded_P6GW`（`_P6GW`，PROVED）**：PICKBALL `pickedBallGrad_of_hgood_C11PB` 的
guarded 孪生——U 数据（梯度）只在 guard 集上要求，seed localization 只在 guard 集上用。证明体逐字（guard
只透传给 `hseed`）。 -/
theorem pickedBallGrad_guarded_P6GW {Cg β : ℝ} {Ct Cgrad : ℝ≥0} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) (n : ℕ) (j : Fin (K n).eventCount) (v : ℝ)
    (hv2 : v < (K n).time j.succ)
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ}
    (hav : (aSeed n : ℝ) ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hvs : v ≤ (σ n : ℝ))
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hseed : PickedBallWindowSeedGuarded_P6GW β Rad (Cg * R n) Ct (K n) j v w
      ((seedTrace n).point j.castSucc h1 h2)
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))) :
    PickedBallGradGuarded_P6GW β Rad (Cg * R n) Ct Cgrad (K n) j v w := by
  intro x hx v' hv' hwin hRx hg ξ
  have hd := hseed x hx v' hv' hwin hRx hg
  have hv'h : v' ≤ (K n).toHistory.horizon :=
    (hv'.2.le.trans hv2.le).trans ((K n).toHistory.time_le_horizon_at _)
  let τ : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v', ((K n).toHistory.time_nonneg _).trans hv'.1.le, hv'h⟩
  have hact : (K n).toHistory.activeStage τ = j.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j τ hv'.1 (hv'.2.trans hv2)
  have hav' : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : τ ≤ σ n := by
    change v' ≤ (σ n : ℝ)
    linarith [hv'.2]
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
    linarith
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k τ) eps C1 C2 x',
        W.capTubeHasNeckChart eps := by
    intro k hk h1' h2' x' hd' hR'
    subst hk
    exact (hgood n τ hav' hvs' hvL' x' hd' hR').1
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j.castSucc τ)
        ((seedTrace n).point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hd
  have hR' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric j.castSucc τ) x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hRx.le
  have hres := key j.castSucc hact h1 h2 x hd' hR'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  obtain ⟨W, -⟩ := hres
  have hR0 : 0 ≤ ((K n).toHistory.event j).incoming.flow.scalar v' x := W.Q_pos.le
  exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **时间导数 guarded（`_P6GW`，PROVED）**：ANCHOR5 `pickedBallDeriv_of_hgood_P6AN5` 的 guarded 孪生
（hgood 时间分量；seed localization 只在 guard 集上用）。证明体逐字。 -/
theorem pickedBallDeriv_guarded_P6GW {Cg β : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (n : ℕ) (j : Fin (K n).eventCount) (v : ℝ)
    (hv2 : v < (K n).time j.succ)
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ}
    (hav : (aSeed n : ℝ) ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hvs : v ≤ (σ n : ℝ))
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ v - β / ((K n).toHistory.event j).incoming.flow.scalar v w)
    (hseed : PickedBallWindowSeedGuarded_P6GW β Rad (Cg * R n) Ct (K n) j v w
      ((seedTrace n).point j.castSucc h1 h2)
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))) :
    ∀ x ∈ riemannianBallOf (((K n).toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt (((K n).toHistory.event j).incoming.flow.scalar v w)),
      ∀ v' ∈ Ioo ((K n).time j.castSucc) v,
      v - β / ((K n).toHistory.event j).incoming.flow.scalar v w ≤ v' →
      Cg * R n < ((K n).toHistory.event j).incoming.flow.scalar v' x →
      GuardKX_C11KX (((K n).toHistory.event j).incoming.flow.scalar v) (Cg * R n) Ct v v' x →
      |derivWithin (fun s => ((K n).toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
        Ctg * ((K n).toHistory.event j).incoming.flow.scalar v' x ^ 2 := by
  intro x hx v' hv' hwin hRx hg
  have hd := hseed x hx v' hv' hwin hRx hg
  have hv'h : v' < (K n).toHistory.horizon :=
    (hv'.2.trans hv2).trans_le ((K n).toHistory.time_le_horizon_at _)
  let τ : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v', ((K n).toHistory.time_nonneg _).trans hv'.1.le, hv'h.le⟩
  have hact : (K n).toHistory.activeStage τ = j.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j τ hv'.1 (hv'.2.trans hv2)
  have hav' : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : τ ≤ σ n := by
    change v' ≤ (σ n : ℝ)
    linarith [hv'.2]
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
    linarith
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      (K n).toHistory.time k < (τ : ℝ) → (τ : ℝ) < (K n).toHistory.horizon →
      |derivWithin (fun s => metricScalarAt ((K n).toHistory.stageMetric k s) x')
          (Iic (τ : ℝ)) τ| ≤
        Ctg * metricScalarAt ((K n).toHistory.stageMetric k τ) x' ^ 2 := by
    intro k hk h1' h2' x' hd' hR'
    subst hk
    exact (hgood n τ hav' hvs' hvL' x' hd' hR').2
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j.castSucc τ)
        ((seedTrace n).point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hd
  have hR' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric j.castSucc τ) x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hRx.le
  have hres := key j.castSucc hact h1 h2 x hd' hR' hv'.1 hv'h
  simp only [ObservedHistory.stageMetric_castSucc_apply] at hres
  exact hres

/-- **hseedTop 的 guarded 替代物在 `n` 处（`_P6GW`，PROVED，无 binder）**：WSBASE
`ObservedHistory.windowSeed_pointAnchor_C11WB` 在 top 点（anchor 时刻 `v := t n = σ n`、slab `j n`、点 `x`
自身）
逐点实例化：`M := max(R(t, x), Cg·R_n)`、窗口尺度 `q := M/Cg`、`Λ := Cg`、深度 `θ`（`1 ≤ 2·Ct·Cg·θ`、
`Ctg·Cg·θ ≤ 1/2`）。guard `2·Ct·M·(t − v′) ≤ 1` ⇒ `t − v′ ≤ θ/q`（guard 深度被 point-anchor 窗覆盖）；
anchor `R(t, x) ≤ Λq = M` 恒真；ExitGuard `d_t(O, x) ≤ dσ + (Lc/2)/√R_n` ⇐ 三角不等式 + `x ∈ B_t(yG,
Rad/√R_n)`、
`2·Rad ≤ Lc`。**不需要** top 球 ceiling（`hanchor0`）、不需要 hpick、不经 `hdistW` 槽 ⇒ ANCHOR4 记录的三条
hseedTop 循环来源都不出现。 -/
theorem pickedBallWindowSeedGuarded_top_P6GW {Cg β Rad : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (n : ℕ) (hR : 0 < R n) {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc)
    (h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n))
    {θ C Lc : ℝ} (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hθ : 0 ≤ θ)
    (hθ2 : 1 ≤ 2 * (Ct : ℝ) * Cg * θ) (hbud : (Ctg : ℝ) * Cg * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Cg ≤ C) (hρC : 2 * Cg ≤ localPropagationRadius C2 ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
      max θ 0 ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Cg)) ≤ L n)
    (hRadLc : 2 * Rad ≤ Lc)
    (hav : (aSeed n : ℝ) ≤ t n - θ / R n) (hθL : θ ≤ L n ^ 2)
    (hlate : 1 ≤ R n * (t n - θ / R n)) :
    PickedBallWindowSeedGuarded_P6GW β Rad (Cg * R n) Ct (K n) (j n) (t n) (yG n)
      ((seedTrace n).point (j n).castSucc h1 h2)
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n))) := by
  intro x hx v' hv' _ _ hg
  unfold GuardKX_C11KX at hg
  have hqM : Cg * R n ≤
      max (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x) (Cg * R n) :=
    le_max_right _ _
  have hxM : ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x ≤
      max (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x) (Cg * R n) :=
    le_max_left _ _
  set M := max (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x) (Cg * R n)
    with hMdef
  have hM : 0 < M := (mul_pos hCg hR).trans_le hqM
  have hCM : Cg * (M / Cg) = M := by field_simp
  have hRq : R n ≤ M / Cg := by
    rw [le_div_iff₀ hCg]
    linarith
  have hθq : θ / (M / Cg) ≤ θ / R n := div_le_div_of_nonneg_left hθ hR hRq
  have hθR : θ / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hθL hR.le
  have hwin : t n - θ / (M / Cg) ≤ v' := by
    have hkey : M * (t n - v') ≤ θ * Cg := by
      have h2' : 2 * (Ct : ℝ) * (M * (t n - v')) ≤ 2 * (Ct : ℝ) * (θ * Cg) := by
        have := hg.trans hθ2
        linarith
      exact le_of_mul_le_mul_left h2' (by positivity)
    have hdiv : t n - v' ≤ θ * Cg / M := by
      rw [le_div_iff₀ hM]
      linarith
    rw [div_div_eq_mul_div]
    linarith
  have hlate' : 1 ≤ R n * (t n - θ / (M / Cg)) := by
    have := mul_le_mul_of_nonneg_left (sub_le_sub_left hθq (t n)) hR.le
    linarith
  have hv1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have hv2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact := (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) hv1 hv2
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      riemannianEDistOf ((K n).toHistory.stageMetric k (σ n)) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (Rad / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' yk hy hx'
    obtain rfl := eq_of_heq hy
    exact (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add le_rfl hx'.le)
  have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (j n).castSucc (σ n)) (yG n)
      (Rad / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply, hσ n, hRn n]
    exact hx
  have hres := key (j n).castSucc hact h1 h2 x (yG n) (hyG n) hx'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hR
  have hxG : riemannianEDistOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (σ n))
      ((seedTrace n).point (j n).castSucc h1 h2) x ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (Lc / 2 / Real.sqrt (R n)) :=
    hres.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsq.le)))
  have hxv : ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) x ≤ Cg * (M / Cg) := by
    rw [hCM, hσ n]
    exact hxM
  have hav' : (aSeed n : ℝ) ≤ (σ n : ℝ) - θ / (M / Cg) := by
    rw [hσ n]
    linarith
  have hσL : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - θ / (M / Cg) := by linarith
  have hlate'' : 1 ≤ R n * ((σ n : ℝ) - θ / (M / Cg)) := by
    rw [hσ n]
    exact hlate'
  have hwin' : (σ n : ℝ) - θ / (M / Cg) ≤ v' := by
    rw [hσ n]
    exact hwin
  have hv'v : v' ≤ (σ n : ℝ) := by
    rw [hσ n]
    exact hv'.2.le
  exact ObservedHistory.windowSeed_pointAnchor_C11WB hC2 (K n).toHistory (haT n) (hsT n) (has n)
    hsmall hclock (seedTrace n) ha₀ hpin (y n) hR (hgood n) (j n) h1 h2 (v := (σ n : ℝ))
    (q := M / Cg) (Λ := Cg) (β := θ) (C := C) hv2 hRq hCg (by rw [hCM]; exact hqM) hbud hC1
    hΛC hρC hRr hL hρL hav' le_rfl hσL hlate'' x hxG hxv v' hwin' hv'v hv'.1

/-- **hseedTop 的 guarded 替代物（序列版，`_P6GW`，PROVED，无 binder）**：对任意 `Rad`，eventually 在 `n` 上
top 点的 `PickedBallWindowSeedGuarded_P6GW β Rad (Cg·R_n) Ct`（guard 常数 `Ct ≥ Ctg`、`Ct > 0`）。常数：
`θ := 1/(2·Ct·Cg)`、`C := max (max 1 (6Cg)) (2Cg/ρ_lp(C2)²)`、`Lc := max (2·Rad) (…)`；eventually 条件由
`hwin θ`、`L → ∞`、`R·r² → ∞`、`R·t → ∞` 给出。前提 = WSBASE point-anchor 的前提（hgood、K0 `hsmall / hclock`、
`hpin`），**全部已在 ANCHOR5 全链 binder 表里**；新增只有 `0 ≤ C2`（witness 常数符号）。 -/
theorem hseedTopGuarded_seq_P6GW {Cg β : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hCtg : (Ctg : ℝ) ≤ Ct) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc)
        (h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      PickedBallWindowSeedGuarded_P6GW β Rad (Cg * R n) Ct (K n) (j n) (t n) (yG n)
        ((seedTrace n).point (j n).castSucc h1 h2)
        (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n))) := by
  intro Rad
  have hlpr := localPropagationRadius_pos hC2
  set θ : ℝ := 1 / (2 * (Ct : ℝ) * Cg) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : 2 * (Ct : ℝ) * Cg * θ = 1 := mul_one_div_cancel (by positivity)
  have hbud : (Ctg : ℝ) * Cg * θ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtg hCg.le) hθ0.le
    linarith
  set C : ℝ := max (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2) with hCdef
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Cg ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Cg ≤ localPropagationRadius C2 ^ 2 * C := by
    have hl2 : 0 < localPropagationRadius C2 ^ 2 := by positivity
    have h := (le_max_right (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2))
    rw [← hCdef, div_le_iff₀ hl2] at h
    linarith
  set Lc : ℝ := max (2 * Rad)
    (2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max θ 0)
    with hLcdef
  filter_upwards [hwin θ hθ0, hL.eventually_ge_atTop (max θ 1),
    hL.eventually_ge_atTop (Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Cg))),
    hRr.eventually_ge_atTop (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))),
    hRt.eventually_ge_atTop (1 + θ)] with n ha hLθ hLc hRrn hRtn
  intro h1 h2
  have hL1 : 1 ≤ L n := (le_max_right θ 1).trans hLθ
  have hθL : θ ≤ L n ^ 2 := by nlinarith [le_max_left θ 1]
  have hav : (aSeed n : ℝ) ≤ t n - θ / R n := by
    rw [← hσ n]
    exact ha
  have hRθ : R n * (θ / R n) = θ := by field_simp [(hRpos n).ne']
  have hlate : 1 ≤ R n * (t n - θ / R n) := by
    rw [mul_sub, hRθ]
    linarith
  exact pickedBallWindowSeedGuarded_top_P6GW K hgood hC2 hjt htj hσ hyG hRn n (hRpos n) (hsmall n)
    (hclock n) ha₀ (hpin n) h1 h2 hCg hCt hθ0.le (le_of_eq hθ1.symm) hbud hC1 hΛC hρC hRrn
    (le_max_right _ _) hLc (le_max_left _ _) hav hθL hlate

/-- **G1 `hgradG_seq_P6GW`（`_P6GW`，PROVED，无 hseedTop）**：ANCHOR4
`hgradL_seq_of_hgood_witness_P6AN4` 的
guarded 孪生——结论 = `∀ Rad, ∀ᶠ n, PickedBallGradGuarded_P6GW β Rad (Cg·R_n) Ct Cgrad`（top 点），来源 =
hgood witness 的 `gradient` 字段（`pickedBallGrad_guarded_P6GW`）+ guarded
seed（`hseedTopGuarded_seq_P6GW`，
WSBASE point-anchor）。hseedTop **不出现**。 -/
theorem hgradG_seq_P6GW {Cg β : ℝ} {Ct Cgrad : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) (hC20 : 0 ≤ C2)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hCtg : (Ctg : ℝ) ≤ Ct) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGradGuarded_P6GW β Rad (Cg * R n) Ct Cgrad (K n) (j n) (t n) (yG n) := by
  intro Rad
  filter_upwards [hseedTopGuarded_seq_P6GW (β := β) K hgood hC20 hjt htj hσ hyG hRn hRpos hRt hwin
    hL hsmall hclock hRr ha₀ hpin hCg hCt hCtg Rad, hwin β hβ,
    hL.eventually_ge_atTop (max β 1)] with n hS ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  have hv1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have hv2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact := (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) hv1 hv2
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc :=
    hact ▸ (K n).toHistory.activeStage_mono (has n)
  have h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n) :=
    hact ▸ (K n).toHistory.activeStage_mono (hsT n)
  have hav' : (aSeed n : ℝ) ≤ t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
      (yG n) := by
    rw [← hRn n, ← hσ n]
    exact ha
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤
      t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
    rw [← hRn n, ← hσ n]
    linarith
  exact pickedBallGrad_guarded_P6GW K hgood hC2 n (j n) (t n) (htj n) h1 h2 (yG n) hav'
    (hσ n).ge hvL' (hS h1 h2)

/-- **`hderTG_seq_P6GW`（`_P6GW`，PROVED，无 hseedTop）**：ANCHOR5 `hderT_seq_of_hgood_P6AN5` 的 guarded
孪生（top slab 时间导数，常数 `Ctg`，只在 guard 点）；seed localization = `hseedTopGuarded_seq_P6GW`。 -/
theorem hderTG_seq_P6GW {Cg β : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC20 : 0 ≤ C2)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hCtg : (Ctg : ℝ) ≤ Ct) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (Rad /
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
        GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) (Cg * R n) Ct
          (t n) v x →
        |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
            (Iic v) v| ≤
          Ctg * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 := by
  intro Rad
  filter_upwards [hseedTopGuarded_seq_P6GW (β := β) K hgood hC20 hjt htj hσ hyG hRn hRpos hRt hwin
    hL hsmall hclock hRr ha₀ hpin hCg hCt hCtg Rad, hwin β hβ,
    hL.eventually_ge_atTop (max β 1)] with n hS ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  have hv1 : (K n).time (j n).castSucc < σ n := by
    rw [hσ n]
    exact hjt n
  have hv2 : ((σ n : ℝ)) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact := (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) hv1 hv2
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc :=
    hact ▸ (K n).toHistory.activeStage_mono (has n)
  have h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n) :=
    hact ▸ (K n).toHistory.activeStage_mono (hsT n)
  have hav' : (aSeed n : ℝ) ≤ t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
      (yG n) := by
    rw [← hRn n, ← hσ n]
    exact ha
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤
      t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
    rw [← hRn n, ← hσ n]
    linarith
  exact pickedBallDeriv_guarded_P6GW K hgood n (j n) (t n) (htj n) h1 h2 (yG n) hav'
    (hσ n).ge hvL' (hS h1 h2)

/-- **hgood ⇒ picked-ball top 数据（guarded，`_P6GW`，PROVED ⇐ 显式 `hgradPB` guarded / `hκPB`）**：AN3
`pickedBallTopData_of_hgood_P6AN3` 的孪生，梯度槽换 `PickedBallGradGuarded_P6GW`。证明体逐字。 -/
theorem pickedBallTopDataGuarded_P6GW {Cg : ℝ} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctime : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop) {β κ : ℝ} {Ct Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ}
    (hgradPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGradGuarded_P6GW β Rad (Cg * R n) Ct Cgrad (K n) (j n) (t n) (yG n))
    (hκPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      (PickedBallWitness_C11PB Rad (Cg * R n) eps C1 C2 (K n) (j n) (t n) (yG n) ∧
        PickedBallGradGuarded_P6GW β Rad (Cg * R n) Ct Cgrad (K n) (j n) (t n) (yG n)) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n) := by
  intro Rad
  filter_upwards [hgradPB Rad, hκPB Rad, hL.eventually_ge_atTop (2 * max Rad 0)] with n hg hk hLn
  have hW := pickedBallWitness_top_of_hgood_P6AN3 K hgood hjt htj hσ hyG hRn hRpos n
    (le_max_right Rad 0) (by linarith)
  have hsub := riemannianBallOf_mono (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
    (yG n) (div_le_div_of_nonneg_right (le_max_left Rad 0)
      (Real.sqrt_nonneg (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
  exact ⟨⟨fun x hx hqx => hW x (hsub hx) hqx, hg⟩, hk⟩

end Producers

section TopLocal

/-- **`topAnchorInputsGuarded_of_local_P6GW`（`_P6GW`，PROVED ⇐ guarded `hlocal`）**：AN2
`topAnchorInputs_of_local_P6AN2` 逐字，`hlocal` 与结论换 guarded 形；证明体逐字。 -/
theorem topAnchorInputsGuarded_of_local_P6GW {β : ℝ} {s t : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters} {T₀ Dsel θsel : ℕ → ℝ}
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hscale : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale)
    (hRlim : Tendsto (fun n => (G n).flow.scalar (t n) (y n)) atTop atTop)
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    (hT₀ : ∀ᶠ n in atTop, T₀ n ≤ t n - β / (G n).flow.scalar (t n) (y n))
    (hDsel : Tendsto Dsel atTop atTop) (hDrad : ∀ n, Dsel n ≤ (p n).modelRadius)
    (hord : ∀ n, 2 ≤ (p n).modelOrder)
    (hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ)
    (hθ : ∀ᶠ n in atTop, β ≤ θsel n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hT : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (B : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      B.point j.succ le_rfl hl = ((records n j hT).static b).window x ∧ ‖x.val‖ < Dsel n + 1 ∧
        t n - (H n).time j.succ ≤ θsel n * (((records n j hT).static b).neck.scale)⁻¹)
    (hlocal : ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧
      ∃ (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi ∧ ∃ Cq : ℝ,
      ∀ Λ Rad : ℝ, 1 ≤ Λ → ∀ᶠ n in atTop,
      ∃ q ρ : ℝ, 0 < q ∧ q ≤ Cq * (G n).flow.scalar (t n) (y n) ∧
      ∃ U : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
        (∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < (G n).flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
            W.capTubeHasNeckChart ε) ∧
        (∀ j : Fin (H n).eventCount,
          ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v z →
          |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
            Ctime * (G n).flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential (G n).flow v x w| ≤
              Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
                Real.sqrt (((G n).flow.base.metric v).inner x w w)) ∧
        (∀ j : Fin (H n).eventCount,
          Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
            (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
              Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi ∧
        (∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
          t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
          let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) T z →
          ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n))) :
    TopAnchorInputsGuarded_P6GW β H hend s G hGi t y := by
  obtain ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, hloc⟩ := hlocal
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq,
    fun _ _ Λ Dcap Rrad ζ₀ Rad hΛ _ hD2 hζ => ⟨0, ?_⟩⟩
  filter_upwards [hloc Λ Rad hΛ, hRlim.eventually_ge_atTop Λ, hRt.eventually_ge_atTop Λ, hT₀,
    hDsel.eventually_ge_atTop Rrad, hacc ζ₀ hζ, hθ] with n hl hR1 hR2 hT hD hac hθn
  obtain ⟨q, ρ, hq, hqC, U, hU, hwit, hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ⟩ := hl
  exact ⟨q, ρ, hq, hqC, hR1, hR2, p n, T₀ n, hT, records n, hcan n, hD.trans (hDrad n), hord n,
    hac, U, hU, hwit, hderE, hderT, hgrad, hpinE, hpinT, hkap, hΛρ,
    fun hc => absurd hc (notCWP_of_hnot_P6AN2 (hscale n) (hD2.trans hD) hθn (hnot n))⟩

/-- **`hlocalGuarded_of_pickedBall_top_P6GW`（`_P6GW`，PROVED ⇐ 显式输入）**：ANCHOR5
`hlocal_of_pickedBall_top_noJ10_P6AN5` 的 guarded 孪生——输入梯度换 `PickedBallGradGuarded_P6GW`、top 时间导数
`hderT` 加 guard；prefix 导数 `hderE`（`hslabSel` 来源）、κ（`hkappa` 来源）、pinching 仍是未 guard 输入，
输出侧 guard 直接丢弃（透传）。 -/
theorem hlocalGuarded_of_pickedBall_top_P6GW {β : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {qthr ρnc : ℕ → ℝ}
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hqthr : ∀ n, 0 < qthr n ∧
      qthr n ≤ Cq * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      (PickedBallWitness_C11PB Rad (qthr n) ε C1 C2 (K n) (j n) (t n) (yG n) ∧
        PickedBallGradGuarded_P6GW β Rad (qthr n) Ctime Cgrad (K n) (j n) (t n) (yG n)) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1))
          (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ B : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
          (((K n).prefixAt (j n).castSucc).time i.succ),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        qthr n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (B.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
              (B.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (B.point i.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (Rad /
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        qthr n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
        GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) (qthr n) Ctime
          (t n) v x →
        |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
            (Iic v) v| ≤
          Ctime * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2) :
    ∃ ε' : ℝ, ε' ≤ coneAccuracy ∧ ∃ κ' C1' C2' : ℝ, 0 < κ' ∧
      ∃ (Ctime' Cgrad' : ℝ≥0) (phi' : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi' ∧
      ∃ Cq' : ℝ, ∀ Λ Rad : ℝ, 1 ≤ Λ → ∀ᶠ n in atTop,
      ∃ q ρ : ℝ, 0 < q ∧
        q ≤ Cq' * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ∧
      ∃ U : Set ((K n).stage (j n).castSucc).Carrier,
        (∀ w ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness
              (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) ε' C1' C2' x,
            W.capTubeHasNeckChart ε') ∧
        (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
          ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1))
            (hf : first ≤ i.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
            (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
          ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ),
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
          q < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (B.point i.castSucc hf (Fin.le_last _)) →
          GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) q Ctime'
            (t n) v z →
          |derivWithin (fun w =>
              (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
                (B.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
              (B.point i.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
          q < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
          GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) q Ctime'
            (t n) v x →
          |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
              (Iic v) v| ≤
            Ctime' * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
          q < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
          GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) q Ctime'
            (t n) v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential ((K n).toHistory.event (j n)).incoming.flow v x w| ≤
              Cgrad' * ((K n).toHistory.event (j n)).incoming.flow.scalar v x *
                Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar v x) *
                Real.sqrt ((((K n).toHistory.event (j n)).incoming.flow.base.metric v).inner x
                  w w)) ∧
        (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
                (((K n).prefixAt (j n).castSucc).time i.succ) ∩
              Ici (t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)))
            phi') ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩
            Ici (t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)))
          phi' ∧
        (∀ (T : ℝ) (hT : ((K n).prefixAt (j n).castSucc).time
              (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) < T)
            (hTs : T < (K n).time (j n).succ), T ≤ t n →
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ T →
          let B := ((K n).prefixAt (j n).castSucc).extendHorizon T
            (((K n).prefixAt_time_last (j n).castSucc) ▸ hT.le)
            (((K n).toHistory.event (j n)).incoming.closedPrefix T hT hTs)
            ((K n).event_initial (j n))
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, ((K n).prefixAt (j n).castSucc).horizon_nonneg.trans
              (((K n).prefixAt_time_last (j n).castSucc) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) q Ctime'
            (t n) T z →
          ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ' * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) := by
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, fun Λ Rad _ => ?_⟩
  filter_upwards [hpb Rad, hderE Rad, hderT Rad, hradii.eventually_ge_atTop Λ] with n hpbn hEn hTn
    hρn
  obtain ⟨⟨hwit, hgrad⟩, hkap⟩ := hpbn
  have hncB := (K n).tested_noncollapse_eventPrefix_P6M (j n) (κ := κ) (ρ := ρnc n)
    (a := t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) (t := t n)
    (riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
    hkap ((K n).prefixAt_time_last _)
  refine ⟨qthr n, ρnc n, (hqthr n).1, (hqthr n).2,
    riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
    fun w hw => hw, fun x hx hqx => hwit x hx hqx,
    fun i first hf z hz B v hv hvw hRv _ => hEn i first hf z hz B v hv hvw hRv,
    fun x hx v hv hvw hRv hg => hTn x hx v hv hvw hRv hg,
    fun x hx v hv hvw hRv hg ξ => hgrad x hx v hv hvw hRv hg ξ,
    fun i v hv => (hpinch n).1 i v hv.1, fun v hv => (hpinch n).2 v hv.1, ?_, hρn⟩
  intro T hT hTs hTt hTa _ _ z hz _
  exact hncB T hT hTs hTt hTa z hz

/-- **`topAnchorInputsGuarded_of_pickedBall_P6GW`（`_P6GW`，PROVED ⇐ 显式输入）**：ANCHOR5
`topAnchorInputs_of_pickedBall_noJ10_P6AN5` 的 guarded 孪生。证明体逐字（换 guarded 组件）。 -/
theorem topAnchorInputsGuarded_of_pickedBall_P6GW {β : ℝ} (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (hRlim : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop)
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {qthr ρnc : ℕ → ℝ}
    (hqthr : ∀ n, 0 < qthr n ∧
      qthr n ≤ Cq * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      (PickedBallWitness_C11PB Rad (qthr n) ε C1 C2 (K n) (j n) (t n) (yG n) ∧
        PickedBallGradGuarded_P6GW β Rad (qthr n) Ctime Cgrad (K n) (j n) (t n) (yG n)) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1))
          (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n)
            (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ B : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
          (((K n).prefixAt (j n).castSucc).time i.succ),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        qthr n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (B.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
              (B.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
            (B.point i.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (Rad /
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        qthr n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
        GuardKX_C11KX (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)) (qthr n) Ctime
          (t n) v x →
        |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
            (Iic v) v| ≤
          Ctime * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2) :
    TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  obtain ⟨hDlim, hDrad, hord, hacc, hθ⟩ := selectionSchedule_noJ10_P6AN5 hβ hpar hθcap
  have hscale0 : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale := fun n i hi b =>
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (hqcan n)))
      (hscale n i hi b)
  exact topAnchorInputsGuarded_of_local_P6GW (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) records
    hcan hscale0 hRlim hRt (hT₀ β) hDlim hDrad hord hacc hθ hnot
    (hlocalGuarded_of_pickedBall_top_P6GW hε hκ hphi hpinch hqthr hradii hpb hderE hderT)

/-- **G1 主定理 `topAnchorInputs_guarded_P6GW`（`_P6GW`，PROVISIONAL：binder = `hslabSel`（J10 残余，阈值形
`Cg·R` 不变，owner SLTLOCAL）+ `hkappa` + hgood + selection supplies + `hR / hRlim` + K0 `hsmall /
hclock / hRr`
+ `hpin` + `0 ≤ C2`；**无 hseedTop**、无 `hqR`、无 `GradientBoundBefore`）**：ANCHOR5
`topAnchorInputs_of_hgood_local_noJ10_P6AN5` 的 guarded 孪生。结论 = `TopAnchorInputsGuarded_P6GW
β`（event 构形）。
梯度 ⇐ `hgradG_seq_P6GW`、top 时间导数 ⇐ `hderTG_seq_P6GW`（二者的 seed localization =
`hseedTopGuarded_seq_P6GW` ⇐ WSBASE point-anchor）；guard 常数 `Ctime + Ctg + 1`。 -/
theorem topAnchorInputs_guarded_P6GW {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    {Cg : ℝ} (hCg : 0 < Cg)
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {ε C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hslabSel : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (Cg * R n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hC20 : 0 ≤ C2) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₁ : ℝ} (ha₁ : 0 ≤ a₁)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₁ + τ') x)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
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
    TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hRlim' : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt' : Tendsto (fun n => R n * t n) atTop atTop := hRt.congr fun n => by rw [hRn n]
  have hCt : (0 : ℝ) < ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) := by positivity
  have hCtg : (Ctg : ℝ) ≤ ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) := by
    push_cast
    linarith [Ctime.coe_nonneg]
  refine topAnchorInputsGuarded_of_pickedBall_P6GW hβ hcan hqcan hpar hscale hθcap hphi hpinch hnot
    hT₀ hRt hRlim' hε hκ (Cq := Cg) (qthr := fun n => Cg * R n) (ρnc := ρnc)
    (Ctime := Ctime + Ctg + 1) (fun n => ⟨mul_pos hCg (hR n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallTopDataGuarded_P6GW K hgood hjt htj hσ hyG hRn hR hL
      (hgradG_seq_P6GW K hgood hC2 hC20 hjt htj hσ hyG hRn hR hβ0 hRt' hwin hL hsmall hclock hRr
        ha₁ hpin hCg hCt hCtg)
      (pickedBallKappa_top_seq_of_hkappa_P6AN3 hjt htj hσ hyG hRn hR hκ.le hkappa))
    (fun Rad => (hderE_of_slabSel_P6AN5 (β := β) (yG := yG) hslabSel Rad).mono
      fun _ h i first hf z hz B v hv hvw hRv =>
        le_add_coe_mul_sq_P6AN5 (le_add_coe_mul_sq_P6AN5 (h i first hf z hz B v hv hvw hRv)))
    (fun Rad => (hderTG_seq_P6GW (β := β) K hgood hC20 hjt htj hσ hyG hRn hR hβ0 hRt' hwin hL hsmall
      hclock hRr ha₁ hpin hCg hCt hCtg Rad).mono fun _ h x hx v hv hvw hRv hg =>
        le_add_coe_mul_sq_P6AN5 (le_add_coe_mul_sq'_P6AN5 (h x hx v hv hvw hRv hg)))
  refine hradii.congr fun n => ?_
  rw [hRn n]

end TopLocal

/-- consumer（G1，`_P6GW`）：guarded top-anchor 输入经 KSWEXIT `shortSLT_guarded_C11KX` 给 G-flow `hanchor0`
（event 构形）——即 `hdistW_eventSlab_guarded_P6GW`（G2）的 top-anchor 半。 -/
example {β : ℝ} (hβ : 0 < β) {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hin : TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG) :
    ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (1 / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
  hanchor0_event_of_topInputsGuarded_P6GW hβ hjt htj hin 1 one_pos

/-- consumer（G1，`_P6GW`）：旧（未 guard）top 输入同样喂 guarded 链（`toGuarded_P6GW`）。 -/
example := @TopAnchorInputs_P6AN2.toGuarded_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
