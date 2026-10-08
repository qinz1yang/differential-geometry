import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorSecondKSW2P6AN2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistWFirstExitP6DW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistWFinalP6DW2

/-!
# ANCHOR 第三轮：`hlocal` 的 picked-ball producer + `hσev` 分类（O-CH11-ANCHOR3，后缀 `_P6AN3`）

接 ANCHOR2 HANDOVER 第 1、3 项（O-CH11-ANCHOR3 简报）。
* **G1（`hlocal` 的 producer）**：`topAnchorInputs_of_local_P6AN2` 的 residual `hlocal`（top 时刻 `t n` 的
  `q, ρ, U ⊇ B(y, Rad/√R)` 上 witness / 导数 / 梯度 / pinching / κ，窗口 `[t − β/R, t]`）在 event 构形
  （`H n = (K n).prefixAt (j n).castSucc`、`G n = (event (j n)).incoming`）由 PICKBALL 合同在 `v := t n`、
  `w := yG n` 处供给：`hlocal_of_pickedBall_top_P6AN3`（PROVED ⇐ 显式输入）。slice → top 接线
  `pickedBallWitness_top_of_hgood_P6AN3`（PROVED：hgood 的 witness 在 top 时刻，seed 余量在 `v = σ`、
  `w ≅ y` 时平凡）；`pickedBallTopData_of_hgood_P6AN3`（witness 半 ⇐ hgood，梯度 / κ 半 = binder
  `hgradPB` / `hκPB`）。组合 `topAnchorInputs_of_pickedBall_P6AN3` / `topAnchorInputs_of_hgood_P6AN3`
  （PROVISIONAL）与 consumer `hanchor0_event_of_hgood_P6AN3`（ShortSLT 由 KSW2 付）。
  **不需要** hpick（`PickedBallTop_C11PB`）；pinching 与导数时间分量都已有来源。**导数分量的来源是 P6CD 层
  `hslab`（prefix `EventSlabsDerivative Ctime qcan`）+ `hderG`（`2 Ctime, 2 qcan`）**——旧的全域导数背景
  （cap-side），不是局域 picked-ball 供给；按外审 R-C11-17 登记为向 `q_sel` 合同迁移的义务（J10GEN）。
* **G2（`hσev` / `hσfin` 分类）**：`hσev_of_selection_P6AN3`（PROVED：`σ = t` 在 `(j n)` 的 event slab 内部 ⇒
  `∀ n, ∃ e, activeStage (σ n) = e.castSucc`）；final 版 `hσfin_of_selection_P6AN3`（PROVED，= HDISTW2
  `hfinalBranch_slab_P6DW2` 重导出）。组合 `hscalW_eventSlab_to_hdistW_P6AN3`
  （G4 `hscalW_eventSlab_of_topInputs_P6AN2` 直接喂 `hdistW_of_firstExit_P6DW`）、
  final 孪生 `hscalW_finalSlab_to_hdistW_P6AN3`（喂
  `hdistW_of_firstExit_final_P6DW2`）、全链 `hdistW_eventSlab_of_pickedBall_P6AN3`
  （`TopAnchorInputs` 换 picked-ball `hpb`）；consumer `example`（`hσev` 不再是参数）。
非循环：`hdistW` 只在结论；前提中无 `hdistW / HU / hgapJ / hclosG / CanonicalLateCore / hspine`
（审计做传递依赖名字扫描）。不声称闭合：剩余 binder 见 state HANDOVER（G3）。
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

section TopLocal

/-- **系数加倍（`_P6AN3`，算术）**：`a ≤ C · b²` ⇒ `a ≤ (2C) · b²`（`C : ℝ≥0`）。hderE 把 P6CD 层
`hslab` 的 `Ctime` 抬到 `hderG` 的 `2 · Ctime`，两条导数界共用一个 `Ctime`。 -/
theorem le_two_mul_coe_mul_sq_P6AN3 {C : ℝ≥0} {a b : ℝ} (h : a ≤ (C : ℝ) * b ^ 2) :
    a ≤ ((2 * C : ℝ≥0) : ℝ) * b ^ 2 := by
  have hb := sq_nonneg b
  have hC := C.coe_nonneg
  push_cast
  nlinarith

/-- **slice → top 接线（`_P6AN3`，PROVED）**：PICKBALL `pickedBallWitness_of_hgood_C11PB` 在
**top 时刻** `v := σ n`（`σ n = t n`）、中心 `w := yG n`（`HEq (y n) (yG n)`）处实例化。中心的 seed 余量
`d_σ(O, yG) ≤ d_σ(O, y) + (L/2)/√R_n` 在 `v = σ`、`w ≅ y` 时是 `a ≤ a + b`（`activeStage σ = (j n)⁻` 经
`activeStage_eq_castSucc_C11PB` 换成 event incoming metric）；`aSeed ≤ σ ≤ σ`、`σ − L²/R ≤ σ` 平凡。
结论 = `PickedBallWitness_C11PB Rad (Cg·R_n)`（top 时刻 `t n`），即 `hlocal` 的 witness 分量（阈值
`Cg·R_n`，`Rad ≤ L_n/2`）。 -/
theorem pickedBallWitness_top_of_hgood_P6AN3 {Cg : ℝ} (K : ℕ → RetainedCoreHistory.{u})
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
    (hRpos : ∀ n, 0 < R n) (n : ℕ) {Rad : ℝ} (hRad0 : 0 ≤ Rad) (hRadL : Rad ≤ L n / 2) :
    PickedBallWitness_C11PB Rad (Cg * R n) eps C1 C2 (K n) (j n) (t n) (yG n) := by
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
  have hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n := by
    have := div_nonneg (sq_nonneg (L n)) (hRpos n).le
    linarith
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      HEq (y n) x' →
      riemannianEDistOf ((K n).toHistory.stageMetric k (σ n)) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' hx
    obtain rfl := eq_of_heq hx
    exact le_self_add
  have hw := key (j n).castSucc hact h1 h2 (yG n) (hyG n)
  rw [ObservedHistory.stageMetric_castSucc_apply] at hw
  have hRw : R n ≤ ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := by
    rw [hσ n, ← hRn n]
  have hres := pickedBallWitness_of_hgood_C11PB K hgood n (j n) (σ n) hv1 hv2 (has n) le_rfl hvL
    h1 h2 (yG n) (hRpos n) hRw hRad0 hRadL hw
  rw [hσ n] at hres
  exact hres

/-- **`hlocal_of_pickedBall_top_P6AN3`（G1，PROVED ⇐ 显式输入；picked-ball 分量为 PROVISIONAL binder）**：
`topAnchorInputs_of_local_P6AN2` 的 residual `hlocal`，在 **event 构形**
（`H n = (K n).prefixAt (j n).castSucc`、`G n = (event (j n)).incoming`、`s n = time (j n).succ`、top
`t n`、`y n = yG n`；`(H n).time last`、`(H n).stage last` 写成 defeq 的 `(K n).time (j n).castSucc`、
`(K n).stage (j n).castSucc`）。逐分量来源：
* `U := B_t(yG, Rad/√R)`（`R = R(t n, yG n)`），`q := max (qthr n) (2 qcan n)`，`ρ := ρnc n`；
* witness / 梯度 ⇐ PICKBALL `PickedBallWitnessGrad_C11PB β Rad (qthr n)`（`v := t n`、`w := yG n`；
  阈值 `qthr ≤ q` 单调；witness 半由 hgood 付见 `pickedBallWitness_top_of_hgood_P6AN3`）；
* κ ⇐ `PickedBallKappa_C11PB β Rad (ρnc n) κ` 经 `tested_noncollapse_eventPrefix_P6M`
  （K 层 → extendHorizon 层，窗口 `a := t − β/R`）；
* `Λ ≤ ρ √R` ⇐ `hradii`；
* 导数 hderE / hderT ⇐ P6CD 层 `hslab`（prefix `EventSlabsDerivative Ctime qcan`）与 `hderG`
  （`DerivativeBoundBefore (2 Ctime) (2 qcan)`），合用 `Ctime′ := 2 Ctime`。**注意**：这是旧的全域导数背景
  （cap-side，阈值 `qcan`），**不是**局域 picked-ball 供给；按外审 R-C11-17 登记为向 `q_sel` 合同迁移的
  义务（J10GEN），本定理只是把它原样接到 `hlocal` 的导数分量；
* pinching ⇐ P6CD 层 `hpinch`（prefix `EventSlabsPinched` ∧ event `j n` 的 `PhiAlmostNonnegative`），限制到
  `∩ Ici (t − β/R)`。
**不需要** `PickedBallTop_C11PB`（hpick）：它不进 ShortSLT / `hlocal` 输入面。 -/
theorem hlocal_of_pickedBall_top_P6AN3 {β : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {qcan qthr ρnc : ℕ → ℝ}
    (hqcan0 : ∀ n, 0 ≤ qcan n)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi)
    (hqthr : ∀ n, 0 < qthr n ∧
      qthr n ≤ Cq * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallWitnessGrad_C11PB β Rad (qthr n) ε C1 C2 Cgrad (K n) (j n) (t n) (yG n) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
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
          |derivWithin (fun w =>
              (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
                (B.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
              (B.point i.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
          q < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
          |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
              (Iic v) v| ≤
            Ctime' * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
          t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
          q < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
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
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ' * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) := by
  refine ⟨ε, hε, κ, C1, C2, hκ, 2 * Ctime, Cgrad, phi, hphi, max Cq 2, fun Λ Rad _ => ?_⟩
  filter_upwards [hpb Rad, hradii.eventually_ge_atTop Λ] with n hpbn hρn
  obtain ⟨⟨hwit, hgrad⟩, hkap⟩ := hpbn
  have hR0 : 0 ≤ ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    (hqcan0 n).trans (hqR n).le
  have hq2 : qcan n ≤ max (qthr n) (2 * qcan n) :=
    le_trans (by linarith [hqcan0 n]) (le_max_right _ _)
  have hqC : max (qthr n) (2 * qcan n) ≤
      max Cq 2 * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    max_le ((hqthr n).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0))
      ((mul_le_mul_of_nonneg_left (hqR n).le (by norm_num : (0 : ℝ) ≤ 2)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0))
  have hncB := (K n).tested_noncollapse_eventPrefix_P6M (j n) (κ := κ) (ρ := ρnc n)
    (a := t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) (t := t n)
    (riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
    hkap ((K n).prefixAt_time_last _)
  exact ⟨max (qthr n) (2 * qcan n), ρnc n, lt_max_of_lt_left (hqthr n).1, hqC,
    riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
    fun w hw => hw, fun x hx hqx => hwit x hx ((le_max_left _ _).trans_lt hqx),
    fun i first hf z _ B v hv _ hRv => le_two_mul_coe_mul_sq_P6AN3
      (hslab n i (Fin.castSucc_lt_last i) _ v hv (hq2.trans_lt hRv)),
    fun x _ v hv _ hRv => hderG n x v hv ((le_max_right _ _).trans_lt hRv),
    fun x hx v hv hvw hRv ξ => hgrad x hx v hv hvw ((le_max_left _ _).trans_lt hRv) ξ,
    fun i v hv => (hpinch n).1 i v hv.1, fun v hv => (hpinch n).2 v hv.1, hncB, hρn⟩

/-- **hgood ⇒ picked-ball top 数据（`_P6AN3`，PROVISIONAL：binder = 梯度半 `hgradPB` + κ 半 `hκPB`）**：
witness 半由 hgood 付（`pickedBallWitness_top_of_hgood_P6AN3`，`Rad₊ := max Rad 0 ≤ L_n/2` eventually，
`L → ∞`；球对 `Rad ≤ Rad₊` 单调），阈值 `qthr n := Cg · R_n`。结论 = `hlocal_of_pickedBall_top_P6AN3` 的
`hpb` 形。`hgradPB` / `hκPB` 的 owner：SEEDCL（`pickedBallGrad_of_firstExit_C11SC`，需 hpick）/
PBKAPPA（`hκPB_of_fresh_C11PK`，需 `PickedBallEndpointRicci_C11PK`）。 -/
theorem pickedBallTopData_of_hgood_P6AN3 {Cg : ℝ} (K : ℕ → RetainedCoreHistory.{u})
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
    (hRpos : ∀ n, 0 < R n) (hL : Tendsto L atTop atTop) {β κ : ℝ} {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ}
    (hgradPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) (j n) (t n) (yG n))
    (hκPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallWitnessGrad_C11PB β Rad (Cg * R n) eps C1 C2 Cgrad (K n) (j n) (t n) (yG n) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n) := by
  intro Rad
  filter_upwards [hgradPB Rad, hκPB Rad, hL.eventually_ge_atTop (2 * max Rad 0)] with n hg hk hLn
  have hW := pickedBallWitness_top_of_hgood_P6AN3 K hgood hjt htj hσ hyG hRn hRpos n
    (le_max_right Rad 0) (by linarith)
  have hsub := riemannianBallOf_mono (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
    (yG n) (div_le_div_of_nonneg_right (le_max_left Rad 0)
      (Real.sqrt_nonneg (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
  exact ⟨⟨fun x hx hqx => hW x (hsub hx) hqx, hg⟩, hk⟩

/-- **`topAnchorInputs_of_pickedBall_P6AN3`（G1 组合，PROVISIONAL：binder = picked-ball `hpb`（梯度 + κ 半；
witness 半可由 hgood 付，见 `topAnchorInputs_of_hgood_P6AN3`）；导数 supplies 为旧全域背景，J10GEN 迁移义务）**：
P6CD / `hscalW_eventSlab_*` 层的 selection supplies（`records / hcan / hqcan / hpar / hscale / hθcap /
hpinch / hslab / hderG / hqR / hnot / hT₀ / hRt`，与 `hscalW_eventSlab_of_topInputs_P6AN2` 同名同形）
+ `hpb` ⇒ event 构形的 `TopAnchorInputs_P6AN2 β`（`β ≤ 1/2`）。= `topAnchorInputs_of_local_P6AN2`
（schedule 部分经 `selectionSchedule_P6AN2`）∘ `hlocal_of_pickedBall_top_P6AN3`。 -/
theorem topAnchorInputs_of_pickedBall_P6AN3 {β : ℝ} (hβ : β ≤ 1 / 2)
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
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {qthr ρnc : ℕ → ℝ}
    (hqthr : ∀ n, 0 < qthr n ∧
      qthr n ≤ Cq * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallWitnessGrad_C11PB β Rad (qthr n) ε C1 C2 Cgrad (K n) (j n) (t n) (yG n) ∧
        PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hqcan0 : ∀ n, 0 ≤ qcan n := fun n => by
    linarith [hqcan n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hRlim, hDlim, hDrad, hord, hacc, hθ, -⟩ := selectionSchedule_P6AN2 hβ hqcan hqR hpar hθcap
  have hscale0 : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale := fun n i hi b =>
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (hqcan n)))
      (hscale n i hi b)
  exact topAnchorInputs_of_local_P6AN2 (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) records
    hcan hscale0 hRlim hRt (hT₀ β) hDlim hDrad hord hacc hθ hnot
    (hlocal_of_pickedBall_top_P6AN3 hε hκ hphi hqcan0 hslab hderG hqR hpinch hqthr hradii hpb)

/-- **`topAnchorInputs_of_hgood_P6AN3`（G1 组合，PROVISIONAL：binder = `hgradPB` + `hκPB`；witness 半由
hgood 付；导数 `hslab / hderG` 为旧全域背景，J10GEN 迁移义务）**：`topAnchorInputs_of_pickedBall_P6AN3` 的 `hpb` 由
`pickedBallTopData_of_hgood_P6AN3` 供（阈值 `qthr n := Cg · R_n`、`Cq := Cg`、`R_n = R(t n, yG n)`）。 -/
theorem topAnchorInputs_of_hgood_P6AN3 {β : ℝ} (hβ : β ≤ 1 / 2)
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
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hgradPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) (j n) (t n) (yG n))
    (hκPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  refine topAnchorInputs_of_pickedBall_P6AN3 hβ hcan hqcan hpar hscale hθcap hphi hpinch hslab hderG
    hqR hnot hT₀ hRt hε hκ (Cq := Cg) (qthr := fun n => Cg * R n) (ρnc := ρnc)
    (fun n => ⟨mul_pos hCg (hRpos n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallTopData_of_hgood_P6AN3 K hgood hjt htj hσ hyG hRn hRpos hL hgradPB hκPB)
  refine hradii.congr fun n => ?_
  rw [hRn n]

/-- **consumer（G1，`hanchor0_event_of_hgood_P6AN3`，PROVISIONAL：binder = `hgradPB` + `hκPB`）**：G-flow
`hanchor0`（top 切片 `t n` 上任意 `A` 的 BCBD，`Q ≥ 2`）⇐ `hanchor0_event_of_topInputs_P6AN2`（ShortSLT 由 KSW2
付，`0 < β`）∘ `topAnchorInputs_of_hgood_P6AN3`。结论 = P6CD `hanchor0` 逐字。 -/
theorem hanchor0_event_of_hgood_P6AN3 {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
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
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
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
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hgradPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) (j n) (t n) (yG n))
    (hκPB : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallKappa_C11PB β Rad (ρnc n) κ (K n) (j n) (t n) (yG n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
  hanchor0_event_of_topInputs_P6AN2 hβ0 hjt htj
    (topAnchorInputs_of_hgood_P6AN3 hβ hjt htj
      hcan hqcan hpar hscale hθcap hphi hpinch hslab hderG hqR hnot
      hT₀ hRt hCg hgood hσ hyG hRn hL hε hκ hradii hgradPB hκPB)

end TopLocal

section SigmaSlab

/-- **`hσev_of_selection_P6AN3`（G2，PROVED）**：event-slab selection 族
（`time (j n)⁻ < t n < time (j n)⁺`）、`Kh = (K ·).toHistory`、`σ n = t n` ⇒
`hdistW_of_firstExit_P6DW` 的 `hσev` 前提**逐字**
`∀ n, ∃ e, activeStage (σ n) = e.castSucc`（取 `e := j n`，`activeStage_eq_castSucc_C11PB`）。 -/
theorem hσev_of_selection_P6AN3 {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (Kh : ℕ → ObservedHistory.{u})
    (hKh : Kh = fun n => (K n).toHistory) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) :
    ∀ n, ∃ e : Fin (Kh n).eventCount, (Kh n).activeStage (σ n) = e.castSucc := by
  subst hKh
  intro n
  refine ⟨j n, (K n).activeStage_eq_castSucc_C11PB (j n) (σ n) ?_ ?_⟩
  · rw [hσ n]
    exact hjt n
  · rw [hσ n]
    exact htj n

/-- **`hσfin_of_selection_P6AN3`（G2 final 版，PROVED）**：final-slab selection 族
（`time last < t n < horizon`）、`Kh = (K ·).toHistory`、`σ n = t n` ⇒
`hdistW_of_firstExit_final_P6DW2` 的 `hσfin ∧ hσlt`（`activeStage σ = Fin.last`、`σ < horizon`）。
= HDISTW2 `hfinalBranch_slab_P6DW2`（树内已有，这里以 ANCHOR 的命名重导出，供 final 组合用）。 -/
theorem hσfin_of_selection_P6AN3 {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n) :
    (∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount) ∧
      ∀ n, (σ n : ℝ) < (Kh n).horizon :=
  hfinalBranch_slab_P6DW2 htl htK Kh hKh σ hσ

/-- **consumer（G2，`_P6AN3`）**：event-slab selection 数据（`hjt / htj / hKh / hσ`）+ `hscalW`（abstract，
= `hscalW_eventSlab_*` 的输出形）⇒ `hdistW` 槽；`hσev` 由 `hσev_of_selection_P6AN3` 付，不再是参数。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hscalW : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  ObservedHistory.hdistW_of_firstExit_P6DW Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r hL
    hsmall hclock hRr hwin ha₀ hpin (hσev_of_selection_P6AN3 hjt htj Kh hKh σ hσ) hscalW

end SigmaSlab

section Composite

/-- **`hscalW_eventSlab_to_hdistW_P6AN3`（G2 组合，PROVISIONAL：binder = `TopAnchorInputs_P6AN2 β`
（event 构形，`β > 0`）+ `hbcadC`；其余为 P6CD 层 supplies 与 P6DW 的 K0 / HI 数据）**：
`ObservedHistory.hscalW_eventSlab_of_topInputs_P6AN2`（G4，ShortSLT 已由 KSW2 付）的输出 = `hscalW` 槽
**逐字**，`hσev` 由 `hσev_of_selection_P6AN3`（`hjt / htj / hσ`）付，二者直接喂
`ObservedHistory.hdistW_of_firstExit_P6DW`；`hR` 由 `hqcan / hqR / hRn` 推出。结论 = `hdistW` 槽逐字。
非循环：`hdistW` 只出现在结论，前提中无 `hdistW / HU / hgapJ / hclosG`。 -/
theorem hscalW_eventSlab_to_hdistW_P6AN3 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
        (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
        (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
        yG) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hin Kh hKh σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn aSeed haT
    hsT has pT seedTrace L r hL hsmall hclock hRr hwin a₁ ha₁ hpin
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact ObservedHistory.hdistW_of_firstExit_P6DW Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r
    hL hsmall hclock hRr hwin ha₁ hpin (hσev_of_selection_P6AN3 hjt htj Kh hKh σ hσ)
    (ObservedHistory.hscalW_eventSlab_of_topInputs_P6AN2 hε hεX hεN hphi hjt htj recordsF ha₀ hHI
      hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin Kh hKh σ y R hσ
      hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT seedTrace
      L)

/-- **`hscalW_finalSlab_to_hdistW_P6AN3`（G2 final 孪生，PROVISIONAL：binder = `TopAnchorInputs_P6AN2 β`
（final 构形，`β > 0`）+ `hbcadC`；其余为 FINCOND 层 supplies 与 K0 / HI 数据）**：
`ObservedHistory.hscalW_final_finalSlab_of_topInputs_P6AN2` 的输出 = `hscalW_final_P6M6`，
`hσfin ∧ hσlt` 由 `hσfin_of_selection_P6AN3`（`htl / htK / hσ`）付，直接喂
`ObservedHistory.hdistW_of_firstExit_final_P6DW2`。
结论 = `hdistW` 槽逐字（final 支）。 -/
theorem hscalW_finalSlab_to_hdistW_P6AN3 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hin : TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
        (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
        (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl)
        (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hin Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn
    aSeed haT hsT has pT seedTrace L r hL hsmall hclock hRr hwin a₁ ha₁ hpin
  have hR : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hslabσ := hσfin_of_selection_P6AN3 htl htK Kh hKh σ hσ
  exact ObservedHistory.hdistW_of_firstExit_final_P6DW2 Kh Tn aSeed σ haT hsT has pT seedTrace y R
    L hR r hL hsmall hclock hRr hwin ha₁ hpin hslabσ.1 hslabσ.2
    (ObservedHistory.hscalW_final_finalSlab_of_topInputs_P6AN2 hε hεX hεN hphi htl htK hG recordsF
      hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin Kh hKh
      σ y R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT
      seedTrace L)

/-- **`hdistW_eventSlab_of_pickedBall_P6AN3`（G1 ∘ G2 全链，PROVISIONAL：binder = picked-ball `hpb`
（梯度 + κ 半；witness 半可由 hgood 付）+ `hbcadC`；导数 `hslab / hderG` 是旧全域背景，J10GEN 迁移义务）**：
`hscalW_eventSlab_to_hdistW_P6AN3` 的 `TopAnchorInputs` 由 `topAnchorInputs_of_pickedBall_P6AN3` 供（同一组
P6CD supplies；pinching 用 `hpinch.1`）。结论 = `hdistW` 槽逐字（event 支）。 -/
theorem hdistW_eventSlab_of_pickedBall_P6AN3 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      {a₀ : ℝ} → (ha₀ : 0 < a₀) →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      {εt : ℝ} → (hεt : εt ≤ coneAccuracy) → {κt C1t C2t Cqt : ℝ} → (hκt : 0 < κt) →
      {Cgradt : ℝ≥0} → {qthr ρt : ℕ → ℝ} →
      (hqthr : ∀ n, 0 < qthr n ∧
        qthr n ≤ Cqt * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hradiit : Tendsto (fun n => ρt n *
        Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop) →
      (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        PickedBallWitnessGrad_C11PB β Rad (qthr n) εt C1t C2t Cgradt (K n) (j n) (t n) (yG n) ∧
          PickedBallKappa_C11PB β Rad (ρt n) κt (K n) (j n) (t n) (yG n)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K j t hjt htj D θcap qcan T₀ p pF δb records recordsF yG a₀ ha₀
    hHI hcan hδF hqcan hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 εt hεt κt C1t
    C2t Cqt hκt Cgradt qthr ρt hqthr hradiit hpb Kh hKh σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc
    hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC
  exact hscalW_eventSlab_to_hdistW_P6AN3 hε hεX hεN hphi hjt htj recordsF ha₀ hHI hcan hδF hqcan
    hpar hscale hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ
    (topAnchorInputs_of_pickedBall_P6AN3 hβ2 hcan hqcan hpar hscale hθcap hphi hpinch hslab
      hderG hqR hnot hT₀ hRt hεt hκt hqthr hradiit hpb) Kh hKh σ y R hσ hyG hRn hr₀ hw hseed hκ ρnc
    hradii hkappa hqs hwitC hbcadC

end Composite

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
