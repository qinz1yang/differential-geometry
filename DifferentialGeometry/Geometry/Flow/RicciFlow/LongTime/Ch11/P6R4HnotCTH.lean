import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TailJT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowDtP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X

/-!
# TRSHNOT G1：R4 中心 (t, y′) 的 hnot（`J10ResE3_JT`，HNR 元组形）——标量失配路线（`_TH`）

TRSJ10 G2 的残余 `R4HnotC_TJ` 是 `J10ResE3_JT K t y′ qK T₀K recordsK`（hnot 于 R4 中心 `(t, y′)`）。
hres 线靠 `¬HasSTC (σ, y)` + `hnotK_seq_a0_HNF` 付 hnot；R4 中心无 `¬HasSTC`（`scalar(t, y′) < 2R <
4R`，`hgood′` 不覆盖）。本文件走**标量失配**：

* trace 点 `(t, y′)` 落入 canonical window、年龄 `≤ θ n / scale`（`θ n = 1 − 1/(n+2)`）、`‖x‖ < n + 2` 时，
  `capWindow_trace_localDt_theta_P6HN`（P6CapWindowDtP6HN，已登记 PROVED）的第一合取子句给
  **标量下界** `c n · scale ≤ scalar(t, y′)`（`c n` 只依赖 `θ n`，在 Dt 常数与窗口半径之前）；
* birth `Nf n · Q n ≤ scale` 与 `scalar(t, y′) < 2 Q n` 合并：`c n · Nf n · Q n ≤ c n · scale ≤ scalar <
  2 Q n`，取 `Nf n ≥ 2 / c n` 即矛盾。

**不用 ε / C1 / C2 / `¬HasSTC`**；Dt 常数 `C := Ctime`（调用方给，任意）。元组 `(Nf, ζ, Rn, δ₀, m₀)`
只依赖 `Ctime`，在一切序列数据之前（HNR 形）。K 帧不命中经 `not_capWindowPoint_prefix_of_late_P6N`
搬到 `J10ResE3_JT` 的 prefix 帧；无 `raiseT0`（birth / HI 前提已是 `∀ n` 形）。

**与 `R4HnotC_TJ` 的差别（必须读）**：TJ 版在 G2 交付前删去了 `recordsF`（全体 events 的 records，
`∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)`）前提，于是 `pF` 成了与 `K` 无关的裸变量，
只剩 delta 界；而 P6LL 桥（`capWindow_trace_localDt_theta_P6HN` 内的 WindowPersistence）必须吃
`recordsF`（只用其 late delta 界）。故本核定理显式带 `recordsF`（HNR 原形，= `hnotK_seq_a0_HNF`
的同名前提）；引擎侧由 `(recQ (ind n) i).rescale_P6M (c n) (hc n)` 供给（见 G2）。
`R4HnotC_TJ` ⇒ 「加 `recordsF` 前提的 `R4HnotC_TJ`」是平凡的；后者的内容由本核证出
（G2 在 R4 完整环境下逐项导出本核前提：`0 < Q`、`t ≤ Tn`、`scalar < 2Q`、事件 slab 导数界、`recordsF` 等）。

主定理 `r4HnotC_core_TH`：显式环境（不依赖 `R4HnotC_TJ` 的长 `let` 环境），结论 `J10ResE3_JT`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- birth 换算（`_TH`）：`Nf ≥ 1/Cb`、`Nf · Q ≤ s`、`0 < Q` ⇒ `Q ≤ Cb · s`。 -/
theorem birth_of_Nf_TH {Nf Cb Q s : ℝ} (hCb : 0 < Cb) (hNf : 1 / Cb ≤ Nf) (hQ : 0 < Q)
    (h : Nf * Q ≤ s) : Q ≤ Cb * s := by
  have h1 : 1 ≤ Cb * Nf := by
    have := mul_le_mul_of_nonneg_left hNf hCb.le
    rwa [mul_one_div_cancel hCb.ne'] at this
  have h2 := mul_le_mul_of_nonneg_left h hCb.le
  nlinarith [mul_le_mul_of_nonneg_right h1 hQ.le]

/-- 标量失配的数值核（`_TH`）：`c · Nf ≥ 2`、`Nf · Q ≤ s`、`c · s ≤ S`、`S < 2 Q`、`0 < Q` ⇒ False。 -/
theorem scalarMismatch_TH {c Nf Q s S : ℝ} (hc : 0 < c) (hNf : 2 / c ≤ Nf) (hQ : 0 < Q)
    (hb : Nf * Q ≤ s) (hlow : c * s ≤ S) (hS : S < 2 * Q) : False := by
  have h2 : 2 ≤ c * Nf := by
    have := mul_le_mul_of_nonneg_left hNf hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have h3 := mul_le_mul_of_nonneg_left hb hc.le
  nlinarith [mul_le_mul_of_nonneg_right h2 hQ.le]

namespace RetainedCoreHistory

/-- **R4 中心 hnot 核（`_TH`，PROVED）**：元组 `(Nf, ζ, Rn, δ₀, m₀)` 只依赖 `Ctime`，先于一切序列数据；
对任意满足 canonical window / 精度 / 半径 / 阶 / HI / late δ / birth（`Nf n · Q n ≤ scale`）/
`1 ≤ a₀K n · scale` / 事件 slab 导数界（同一 `Q`）/ `recordsF` 的 K 帧数据，中心 `(t, y′)`（标量
`< 2 Q n`）的 `J10ResE3_JT`。 -/
theorem r4HnotC_core_TH (Ctime : ℝ≥0) :
    ∃ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ), (∀ n, 0 < Nf n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n, 0 < δ₀ n) ∧
    ∀ {K : ℕ → RetainedCoreHistory.{u}} (t : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y' : ∀ n, ((K n).toHistory.stageAt (t n)).Carrier) {Q Tn : ℕ → ℝ},
      (∀ n, 0 < Q n) → (∀ n, (t n : ℝ) ≤ Tn n) →
      (∀ n, metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (t n))
        (t n)) (y' n) < 2 * Q n) →
      (∀ n (i : Fin (K n).eventCount),
        ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
          (min ((K n).time i.succ) (Tn n))) →
    ∀ {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (qK n)}
      {pF : ℕ → CutoffParameters} {a₀K : ℕ → ℝ},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (qK n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (qK n).modelRadius) →
      (∀ n, m₀ n ≤ (qK n).modelOrder) →
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
        -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ (n : ℕ) i hi b, Nf n * Q n ≤ ((recordsK n i hi).static b).neck.scale) →
      (∀ (n : ℕ) i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) →
      J10ResE3_JT K t y' qK T₀K recordsK := by
  have h1 := fun n : ℕ => capWindow_trace_localDt_theta_P6HN.{u} (1 - 1 / ((n : ℝ) + 2))
    (by linarith [half_le_thetaCap_HNF n]) (thetaCap_lt_one_HNF n)
  choose c C' hc hC' hall using h1
  choose Cb hCb hD using fun n => hall n Ctime
  choose Rw hRw m₀ hm₀ ζ δ₀ hζ hζ2 hδ h4 using fun n : ℕ => hD n ((n : ℝ) + 1) (by positivity)
  refine ⟨fun n => max 1 (max (1 / Cb n) (2 / c n)), ζ, Rw, δ₀, m₀,
    fun n => lt_of_lt_of_le one_pos (le_max_left _ _), hζ, hδ, ?_⟩
  intro K t y' Q Tn hQ htT hscal hslab qK T₀K recordsK pF a₀K recordsF hcanK hacc hrad hord hHI
    hδF hbirth hbirthA n jn hjt htj yG hyG
  refine (K n).not_capWindowPoint_prefix_of_late_P6N jn.castSucc (recordsK n) yG ?_
  rintro ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩
  have hq : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hNf1 : 1 / Cb n ≤ max 1 (max (1 / Cb n) (2 / c n)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hNf2 : 2 / c n ≤ max 1 (max (1 / Cb n) (2 / c n)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hbirth' : Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale :=
    birth_of_Nf_TH (hCb n) hNf1 (hQ n) (hbirth n i hi b)
  -- 前缀导数界：event slab `< jn` 与 `jn` 的 slab 到 `t n`
  have hEv : (K n).EventSlabsDerivative Ctime (Q n) jn.castSucc := by
    intro j' hj'
    have hle : (K n).time j'.succ ≤ (K n).time jn.castSucc :=
      (K n).time_strictMono.monotone (Fin.castSucc_lt_iff_succ_le.mp hj')
    have hmin : (K n).time j'.succ ≤ Tn n := (hle.trans hjt.le).trans (htT n)
    have := hslab n j'
    rwa [min_eq_left hmin] at this
  have hcur : ((K n).toHistory.event jn).incoming.DerivativeBoundBefore Ctime (Q n) (t n) :=
    ((K n).toHistory.event jn).incoming.derivativeBoundBefore_mono (le_min htj.le (htT n))
      (hslab n jn)
  have hlow := (h4 n (K n) (recordsK n) (hcanK n) (hrad n) (hord n) (hacc n) (recordsF n) (δ₀ n)
    (hδF n) le_rfl (Q n) (a₀K n) (1 - 1 / ((n : ℝ) + 2)) (hQ n) le_rfl (fun x => (hHI n x).1)
    (fun x => (hHI n x).2) jn.castSucc ((K n).time jn.succ) ((K n).toHistory.event jn).incoming
    ((K n).event_initial jn) hEv (t n) hjt htj hcur i hi hl yG A b x hx hage hxn hbirth'
    (hbirthA n i hi b)).1
  have hact : (K n).toHistory.activeStage (t n) = jn.castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6X jn (t n) hjt.le htj
  have hsc := (K n).scalar_of_incoming_P6X jn hact.symm (t n : ℝ) yG (y' n) hyG
  refine scalarMismatch_TH (hc n) hNf2 (hQ n) (hbirth n i hi b) hlow ?_
  rw [← hsc]
  exact hscal n

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
