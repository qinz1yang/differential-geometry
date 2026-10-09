import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthP6AN4

/-!
# ANCHOR 第五轮：ANCHOR 路径去 `hqR`（q_sel 版 `hlocal` / top-anchor 接口）（O-CH11-ANCHOR5，后缀 `_P6AN5`）

外审 R-C11-18 Q1.2 第三点 / D-2(iii)：`hlocal_of_pickedBall_top_P6AN3`（AN3:140–155）用 `hqR : qcan < R`
（AN3:236–252）证 `max qthr (2·qcan) ≤ max Cq 2 · R`；ANCHOR4 `topAnchorInputs_of_hgood_local_P6AN4` 与全链
`hdistW_eventSlab_of_hgood_local_P6AN4` 原样传入。本文件给 **无 `hqR`** 的孪生，口径同 J10GEN / J10CORE
（`kRouteHICond_noJ10_P6JG`：driver 取 `qcan := Cg·R`，导数在阈值 `Cg·R` 处由 hgood 供给）。
**不声称 anchor 已去 J10**：`hqR` binder 与 `qcan < R` 比较已消去，但 prefix slab 导数仍由显式 binder `hslabSel`
付——**J10 残余（阈值换皮）**，见下 (A′)。
* **(A) 阈值比较 → q_sel**：`hlocal_of_pickedBall_top_noJ10_P6AN5` 取 `q := qthr n`（= q_sel，实例
  `Cg·R_n`），`q ≤ Cq·R` 直接来自 `hqthr`；导数两子句改为 **q_sel 阈值的局域 binder** `hderE`（prefix slabs）/
  `hderT`（event slab），常数 `Ctime′ := Ctime`。旧 `hslab`（`EventSlabsDerivative Ctime qcan`）/ `hderG`
  （`2·Ctime, 2·qcan`）**完全退出 `hlocal`**，只作 cap-side B5 输入（depth driver 内部），不与 `R` 比较。
  结论 = AN3 `hlocal` 逐字。
* **导数来源**：event slab ⇐ hgood **时间分量**（`HasSpatialCanonicalTimeControl` 的 `Ctime`）+ hseedTop 定位
  （`pickedBallDeriv_of_hgood_P6AN5` → `hderT_of_hgood_witness_P6AN5` →
  `hderT_seq_of_hgood_P6AN5`，PROVED；与 ANCHOR4 梯度 `hgradL_*_P6AN4` 同手法）。
* **(A′) J10 残余（阈值换皮）**：prefix slabs 的导数由显式全局 binder
  `hslabSel : EventSlabsDerivative Ctime (Cg·R_n)` 付（`hderE_of_slabSel_P6AN5`，PROVED 接线）。它本质是
  "slab 导数阈值 ≤ Cg·R"，即 J10 的换皮；anchor 的前 slab 导数不能由 first-exit producer 付（那是 anchor
  自身结论，循环）。诚实修复 = SLT 核 `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M`
  的孪生（导数槽只在坏点尺度 `1/R(z)` 的 trace 上要），repair target，owner 与 J10GEN3 共用。
* **(B) schedule / 正性 → binder**：`selectionSchedule_P6AN2` 的 `R → ∞` 改由 binder `hRlim`，
  `0 < R_n` 由 binder `hR`（`selectionSchedule_noJ10_P6AN5` = 去 R 部分的副本）。
* 组合：`topAnchorInputs_of_pickedBall_noJ10_P6AN5`（AN3:306 孪生）、
  `topAnchorInputs_of_hgood_local_noJ10_P6AN5`（AN4:283 孪生；witness / 梯度 / 时间导数 ⇐ hgood + hseedTop，
  κ ⇐ `hkappa`，prefix 导数 ⇐ `hslabSel`（J10 残余））；top-anchor `hanchor0` 经 KSW2
  `hanchor0_event_of_topInputs_P6AN2`（本身无 `hqR`）。
* **(C) depth driver（lead 23:0x 裁定 (c1)）**：全链 `hdistW_eventSlab_of_hgood_local_noJ10_P6AN5` 的
  `hscalW` 半原来经 AN2 G4 → 旧 driver `exists_subseq_htraced_extendAt_late_cond_P6CD`
  （P6KRouteCondP6CD:147–163 用 `hqR` 得 `hR / hRlim / hqcan2`），是 driver 层 J10，不在 anchor 内。
  这里改为显式 binder **`hdepthA`**
  （`hanchor0 ⇒` `hdepth_toHistory_eventSlab_P6AN2` 的结论形）；旧链（带 `hqR`）可填此槽（审计
  `O-CH11-ANCHOR5G2Audit.lean` 的 example）。repair target = J10GEN2A 的无 J10 late_cond driver
  （`kRouteHICond_noJ10_full_P6JA` 口径），已发 J10GEN2A。
非循环：前提中无 `hdistW` 槽 / `HU` / `hgapJ` / `hclosG` / `CanonicalLateCore` / `hspine` /
`GradientBoundBefore`，也无 `qcan < R` 形比较（审计 deny 扫描）。hseedTop 仍 BLOCKED（owner KSWEXIT）。
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

section Arith

/-- **系数单调（`_P6AN5`，算术）**：`a ≤ C · b²` ⇒ `a ≤ (C + C′) · b²`（`C C′ : ℝ≥0`）。 -/
theorem le_add_coe_mul_sq_P6AN5 {C C' : ℝ≥0} {a b : ℝ} (h : a ≤ (C : ℝ) * b ^ 2) :
    a ≤ ((C + C' : ℝ≥0) : ℝ) * b ^ 2 := by
  have hb := sq_nonneg b
  have hC := C'.coe_nonneg
  push_cast
  nlinarith

/-- **系数单调（`_P6AN5`，算术，右项）**：`a ≤ C′ · b²` ⇒ `a ≤ (C + C′) · b²`。 -/
theorem le_add_coe_mul_sq'_P6AN5 {C C' : ℝ≥0} {a b : ℝ} (h : a ≤ (C' : ℝ) * b ^ 2) :
    a ≤ ((C + C' : ℝ≥0) : ℝ) * b ^ 2 := by
  have hb := sq_nonneg b
  have hC := C.coe_nonneg
  push_cast
  nlinarith

/-- **schedule（`_P6AN5`，PROVED）**：`selectionSchedule_P6AN2` 去掉 `R → ∞` 与 `0 < qcan` 两项的副本——
不再需要 `hqR`（`R → ∞` 改为调用方 binder `hRlim`）。`hpar / hθcap / β ≤ 1/2` ⇒ `Dsel → ∞`、
`Dsel ≤ modelRadius`、阶 `≥ 2`、精度 → 0、eventually `β ≤ θcap`。 -/
theorem selectionSchedule_noJ10_P6AN5 {β : ℝ} (hβ : β ≤ 1 / 2) {p : ℕ → CutoffParameters}
    {D θcap : ℕ → ℝ} {δb : ℕ → ℝ}
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) :
    Tendsto D atTop atTop ∧ (∀ n, D n ≤ (p n).modelRadius) ∧
      (∀ n, 2 ≤ (p n).modelOrder) ∧ (∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ) ∧
      (∀ᶠ n in atTop, β ≤ θcap n) := by
  refine ⟨tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop, fun n => (hpar n).2.2.1,
    fun n => le_trans (Nat.le_add_left 2 n) (hpar n).2.2.2.1, fun ζ hζ => ?_,
    Eventually.of_forall fun n => ?_⟩
  · linarith [(hpar n).2.1]
  · filter_upwards [(tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 ζ hζ] with n hn
    exact (hpar n).1.trans hn.le
  · have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith [hθcap n]

end Arith

section DerivLocal

/-- **时间导数 ⇐ hgood + hseed（`_P6AN5`，PROVED）**：PICKBALL `pickedBallGrad_of_hgood_C11PB` 的时间分量
孪生。窗口 `[v − β/q, v)` 上球点 `x` 在 `R(v′, x) > Cg·R_n` 处，hseed 把 `x` 放进 hgood 的 seed 域，hgood 的
`HasSpatialCanonicalTimeControl` **时间分量**（`time (activeStage v′) < v′ < horizon` 时
`|∂_t R| ≤ Ctg R²`）经 `stageMetric_castSucc_apply` 换成 event incoming flow。阈值 = `Cg·R_n`（q_sel）。 -/
theorem pickedBallDeriv_of_hgood_P6AN5 {Cg β : ℝ} (K : ℕ → RetainedCoreHistory.{u})
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
    (hseed : PickedBallWindowSeed_C11PB β Rad (Cg * R n) (K n) j v w
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
      |derivWithin (fun s => ((K n).toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
        Ctg * ((K n).toHistory.event j).incoming.flow.scalar v' x ^ 2 := by
  intro x hx v' hv' hwin hRx
  have hd := hseed x hx v' hv' hwin hRx
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

/-- **top 时间导数 ⇐ hgood + hseedTop 在 `n` 处（`_P6AN5`，PROVED）**：ANCHOR4
`hgradL_of_hgood_witness_P6AN4` 的时间导数孪生（top 点 `v := t n`、`w := yG n`、阈值 `Cg·R_n`），结论 =
`hlocal_of_pickedBall_top_noJ10_P6AN5` 的 `hderT` 在 `n` 处（`qthr n := Cg·R_n`、`Ctime := Ctg`）。窗口球点
进 hgood 区域由 hseedTop（经 `pickedBallWindowSeed_top_of_window_P6AN4`）。 -/
theorem hderT_of_hgood_witness_P6AN5 {Cg β Rad : ℝ}
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
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (n : ℕ) (hav : (aSeed n : ℝ) ≤ σ n - β / R n)
    (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n - β / R n)
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
        (yG n)
        (Rad /
          Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
          (Iic v) v| ≤
        Ctg * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 := by
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
  have hseed := pickedBallWindowSeed_top_of_window_P6AN4 K (haT := haT) (hsT := hsT) (has := has)
    hjt htj hσ hyG hRn n h1 h2 hW
  have hav' : (aSeed n : ℝ) ≤ t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
      (yG n) := by
    rw [← hRn n, ← hσ n]
    exact hav
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤
      t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
    rw [← hRn n, ← hσ n]
    exact hvL
  exact pickedBallDeriv_of_hgood_P6AN5 K hgood n (j n) (t n) (htj n) h1 h2 (yG n) hav'
    (hσ n).ge hvL' hseed

/-- **序列版（`_P6AN5`，PROVED ⇐ hgood + hseedTop）**：结论 = `hlocal_of_pickedBall_top_noJ10_P6AN5` 的
`hderT` 槽逐字（`qthr n := Cg·R_n`、`Ctime := Ctg`）。时间域同 `hgradL_seq_of_hgood_witness_P6AN4`。 -/
theorem hderT_seq_of_hgood_P6AN5 {Cg β : ℝ}
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
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (Rad /
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
        t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
        Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
        |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
            (Iic v) v| ≤
          Ctg * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 := by
  intro Rad
  filter_upwards [hseedTop Rad, hwin β hβ, hL.eventually_ge_atTop (max β 1)] with n hW ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  exact hderT_of_hgood_witness_P6AN5 K hgood hjt htj hσ hyG hRn n ha (by linarith) hW

/-- **prefix 导数 ⇐ 全局前缀背景 `hslabSel`（`_P6AN5`，PROVED 接线；输入是 J10 残余（阈值换皮））**：
`hslabSel`（prefix `EventSlabsDerivative Ctime (qthr n)`）⇒ `hlocal_of_pickedBall_top_noJ10_P6AN5` 的
`hderE` 槽
（球点 / trace / 窗口条件不用）。`hslabSel` 在 `qthr := Cg·R` 时 = "slab 导数阈值 ≤ Cg·R"，是 J10 的换皮，
**不是**局域供给；诚实修复 = SLT 核 `RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M`
  的孪生（导数槽只在坏点尺度 `1/R(z)` 的 trace 上要），repair target，owner 与 J10GEN3 共用。 -/
theorem hderE_of_slabSel_P6AN5 {β : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {Ctime : ℝ≥0} {qthr : ℕ → ℝ}
    (hslabSel : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qthr n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
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
            (B.point i.castSucc hf (Fin.le_last _)) ^ 2 :=
  fun _ => Eventually.of_forall fun n i _ _ _ _ _ v hv _ hRv =>
    hslabSel n i (Fin.castSucc_lt_last i) _ v hv hRv

end DerivLocal

section TopLocal

/-- **`hlocal_of_pickedBall_top_noJ10_P6AN5`（G1，PROVED ⇐ 显式输入；无 `hqR`）**：AN3
`hlocal_of_pickedBall_top_P6AN3` 的结论**逐字**（event 构形）。与 AN3 的差别只在阈值与导数来源：
`q := qthr n`（q_sel；`hqthr` 直接给 `0 < q ≤ Cq·R`，**不**取 `max qthr (2·qcan)`、**不**比较 `qcan` 与 `R`）；
导数两子句由 q_sel 阈值的局域 binder `hderE`（prefix slabs，经 trace）/ `hderT`（event slab）给，
`Ctime′ := Ctime`（不再加倍）。witness / 梯度 / κ / pinching / `Λ ≤ ρ√R` 同 AN3。来源：`hderT` ⇐
`hderT_seq_of_hgood_P6AN5`（hgood 时间分量 + hseedTop），`hderE` ⇐
`hderE_of_slabSel_P6AN5`（`hslabSel`，**J10 残余（阈值换皮）**）。本定理自身只是局域槽接线。 -/
theorem hlocal_of_pickedBall_top_noJ10_P6AN5 {β : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
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
      PickedBallWitnessGrad_C11PB β Rad (qthr n) ε C1 C2 Cgrad (K n) (j n) (t n) (yG n) ∧
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
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, fun Λ Rad _ => ?_⟩
  filter_upwards [hpb Rad, hderE Rad, hderT Rad, hradii.eventually_ge_atTop Λ] with n hpbn hEn hTn
    hρn
  obtain ⟨⟨hwit, hgrad⟩, hkap⟩ := hpbn
  have hncB := (K n).tested_noncollapse_eventPrefix_P6M (j n) (κ := κ) (ρ := ρnc n)
    (a := t n - β / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) (t := t n)
    (riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))))
    hkap ((K n).prefixAt_time_last _)
  exact ⟨qthr n, ρnc n, (hqthr n).1, (hqthr n).2,
    riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
    fun w hw => hw, fun x hx hqx => hwit x hx hqx,
    fun i first hf z hz B v hv hvw hRv => hEn i first hf z hz B v hv hvw hRv,
    fun x hx v hv hvw hRv => hTn x hx v hv hvw hRv,
    fun x hx v hv hvw hRv ξ => hgrad x hx v hv hvw hRv ξ,
    fun i v hv => (hpinch n).1 i v hv.1, fun v hv => (hpinch n).2 v hv.1, hncB, hρn⟩

/-- **`topAnchorInputs_of_pickedBall_noJ10_P6AN5`（G1 组合，PROVISIONAL：binder = `hpb` + q_sel 导数
`hderE / hderT` + `hRlim`；无 `hqR`、无 `hslab / hderG`）**：AN3 `topAnchorInputs_of_pickedBall_P6AN3`
的孪生。
schedule 经 `selectionSchedule_noJ10_P6AN5`（`R → ∞` = binder `hRlim`），`hlocal` 经
`hlocal_of_pickedBall_top_noJ10_P6AN5`。结论 = event 构形 `TopAnchorInputs_P6AN2 β` 逐字。 -/
theorem topAnchorInputs_of_pickedBall_noJ10_P6AN5 {β : ℝ} (hβ : β ≤ 1 / 2)
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
      PickedBallWitnessGrad_C11PB β Rad (qthr n) ε C1 C2 Cgrad (K n) (j n) (t n) (yG n) ∧
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
        |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x)
            (Iic v) v| ≤
          Ctime * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2) :
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  obtain ⟨hDlim, hDrad, hord, hacc, hθ⟩ := selectionSchedule_noJ10_P6AN5 hβ hpar hθcap
  have hscale0 : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale := fun n i hi b =>
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (hqcan n)))
      (hscale n i hi b)
  exact topAnchorInputs_of_local_P6AN2 (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) records
    hcan hscale0 hRlim hRt (hT₀ β) hDlim hDrad hord hacc hθ hnot
    (hlocal_of_pickedBall_top_noJ10_P6AN5 hε hκ hphi hpinch hqthr hradii hpb hderE hderT)

/-- **`topAnchorInputs_of_hgood_local_noJ10_P6AN5`（G1 组合，PROVISIONAL：binder = hseedTop（BLOCKED，owner
KSWEXIT）+ `hslabSel`（J10 残余（阈值换皮））+ `hkappa` + hgood + selection supplies + `hR / hRlim`；无 `hqR`、无
`hslab / hderG`、无 `GradientBoundBefore`）**：ANCHOR4 `topAnchorInputs_of_hgood_local_P6AN4` 的孪生。阈值
`qthr n := Cg·R_n`、`Cq := Cg`；witness ⇐ hgood（`pickedBallTopData_of_hgood_P6AN3`）、梯度 ⇐ hgood +
hseedTop（`hgradL_seq_of_hgood_witness_P6AN4`）、event 时间导数 ⇐ hgood + hseedTop
（`hderT_seq_of_hgood_P6AN5`）、prefix 导数 ⇐ `hslabSel`（`hderE_of_slabSel_P6AN5`）、κ ⇐ `hkappa`
（`pickedBallKappa_top_seq_of_hkappa_P6AN3`）；两条导数合用
`Ctime + Ctg`。结论 = `TopAnchorInputs_P6AN2 β`（event 构形）逐字。 -/
theorem topAnchorInputs_of_hgood_local_noJ10_P6AN5 {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
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
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
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
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (j n).castSucc)
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).time (j n).succ)
      (fun n => ((K n).toHistory.event (j n)).incoming) (fun n => (K n).event_initial (j n)) t
      yG := by
  have hRlim' : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  refine topAnchorInputs_of_pickedBall_noJ10_P6AN5 hβ hcan hqcan hpar hscale hθcap hphi hpinch hnot
    hT₀ hRt hRlim' hε hκ (Cq := Cg) (qthr := fun n => Cg * R n) (ρnc := ρnc)
    (Ctime := Ctime + Ctg) (fun n => ⟨mul_pos hCg (hR n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallTopData_of_hgood_P6AN3 K hgood hjt htj hσ hyG hRn hR hL
      (hgradL_seq_of_hgood_witness_P6AN4 K hgood hC2 hjt htj hσ hyG hRn hR hβ0 hwin hL hseedTop)
      (pickedBallKappa_top_seq_of_hkappa_P6AN3 hjt htj hσ hyG hRn hR hκ.le hkappa))
    (fun Rad => (hderE_of_slabSel_P6AN5 (β := β) (yG := yG) hslabSel Rad).mono
      fun _ h i first hf z hz B v hv hvw hRv =>
        le_add_coe_mul_sq_P6AN5 (h i first hf z hz B v hv hvw hRv))
    (fun Rad => (hderT_seq_of_hgood_P6AN5 K hgood hjt htj hσ hyG hRn hR hβ0 hwin hL hseedTop
      Rad).mono fun _ h x hx v hv hvw hRv => le_add_coe_mul_sq'_P6AN5 (h x hx v hv hvw hRv))
  refine hradii.congr fun n => ?_
  rw [hRn n]

end TopLocal

section LocalChain

/-- **`hdistW_eventSlab_of_hgood_local_noJ10_P6AN5`（G1 全链 (c1)，PROVISIONAL：binder = `hdepthA`（depth
driver 槽，repair = J10GEN2A 无 J10 late_cond driver）+ hseedTop（BLOCKED，KSWEXIT）+ `hslabSel`（J10 残余
（阈值换皮），repair = SLT 核 `eventually_scalar_bound_at_distance_window_P6M` 孪生，owner 与 J10GEN3 共用）
+ `hkappa` + hgood + selection supplies + P6DW K0 / HI + `hR / hRlim`；**无 `hqR`**）**：ANCHOR4
`hdistW_eventSlab_of_hgood_local_P6AN4` 的孪生。top-anchor 半：
`topAnchorInputs_of_hgood_local_noJ10_P6AN5` →
KSW2 `hanchor0_event_of_topInputs_P6AN2`；depth 半：`hdepthA hanchor0` 喂
`hscalW_eventually_of_subseqDriver_P6AN2`（stage-birth top 在其内部排除）；`hσev` 由
`hσev_of_selection_P6AN3`；合成 `hdistW_of_firstExit_P6DW`。旧 depth 链的 P6CD supplies
（`recordsF / hHI / hδF / hslab / hderG / hseed / hwitC / hbcadC / hqs` 与 `hqR`）不再出现在前提里，
都收进 `hdepthA` 的 producer（旧的带 `hqR` 的 `hdepth_toHistory_eventSlab_P6AN2` 可填，见审计 example）。
结论 = `hdistW` 槽逐字（event 支）。 -/
theorem hdistW_eventSlab_of_hgood_local_noJ10_P6AN5 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
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
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
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
      (hdepthA : (∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
          ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
              (yG n)
              (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
            ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
              Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      (∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (Cg * R n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (Kh n).time ((Kh n).activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
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
  intro Ctime phi hphi K j t hjt htj D θcap qcan T₀ p δb records yG hcan hqcan hpar hscale hθcap
    hpinch hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R hσ hyG hRn hR hRlim κ hκ ρnc hradii hkappa hdepthA
    Tn aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood hslabSel Cgrad hC2
    hseedTop hL hsmall hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  have hin := topAnchorInputs_of_hgood_local_noJ10_P6AN5 hβ hβ2 hjt htj hcan hqcan hpar hscale
    hθcap hphi hpinch hnot hT₀ hRt hCg hgood hσ hyG hRn hR hRlim hslabSel hL hεg hκ hradii hC2 hwin
    hseedTop hkappa
  have hanc := hanchor0_event_of_topInputs_P6AN2 hβ hjt htj hin
  exact ObservedHistory.hdistW_of_firstExit_P6DW (fun n => (K n).toHistory) Tn aSeed σ haT hsT has
    pT seedTrace y R L hR r hL hsmall hclock hRr hwin ha₁ hpin
    (hσev_of_selection_P6AN3 hjt htj (fun n => (K n).toHistory) rfl σ hσ)
    (ObservedHistory.hscalW_eventually_of_subseqDriver_P6AN2 (fun n => (K n).toHistory) Tn aSeed σ
      haT hsT has pT seedTrace y R L hR (fun φ hφ _ => hdepthA hanc φ hφ))

end LocalChain

/-- consumer（G1，`_P6AN5`）：q_sel 阈值 `Cg·R_n` 满足 `hqthr` 形（`0 < Cg·R ≤ Cg·R`），无需比较 `qcan` 与 `R`。 -/
example {Cg R : ℝ} (hCg : 0 < Cg) (hR : 0 < R) : 0 < Cg * R ∧ Cg * R ≤ Cg * R :=
  ⟨mul_pos hCg hR, le_rfl⟩

/-- consumer（G1，`_P6AN5`）：event 支 top-anchor 接口无 `hqR`——`topAnchorInputs_of_hgood_local_noJ10_P6AN5`
喂 KSW2 adapter 得 G-flow `hanchor0`（全链 `hdistW_eventSlab_of_hgood_local_noJ10_P6AN5` 即如此使用）。 -/
example := @hanchor0_event_of_topInputs_P6AN2.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
