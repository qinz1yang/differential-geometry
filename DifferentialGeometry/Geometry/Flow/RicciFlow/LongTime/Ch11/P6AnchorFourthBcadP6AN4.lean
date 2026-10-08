import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowContractC11SH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FinalCondP6FCSlice

/-!
# ANCHOR 第四轮 G3：`hbcadC`（SHALLOW T0）现状核对（O-CH11-ANCHOR4，后缀 `_P6AN4`；不证新分析）

ANCHOR 链（event：`hdistW_eventSlab_of_hgood_local_P6AN4`；final：
`hdistW_finalSlab_of_hgood_local_P6AN4` / `hdistW_finalSlab_of_pickedBall_P6AN4`）的 `hbcadC` binder
= SHALLOW T0 `ShallowBcadC_C11SH Kh σ y R` 逐字（driver 第二版 `hbcadC`，`Kh = (K ·).toHistory`，
量词序 `∀ A Dd ∃ C ∀ φ σ′ Dw T Kc`，`σ′ < 0` 严格负偏移）。

**T1 ⇒ T0（两条，都树内已证）**：
* event：P6L3 `shallowBcadC_of_sliceRC_C11SH`（要 `σ n < time last`）；
* **任意 σ（含 final slab）**：P6FC `hbcadC_of_slice_dichotomy_open_final_P6FC`——**不要**
  `σ < time last`，T1 前件形与 `ShallowSliceRC_C11SH` 定义等。本文件
  `shallowBcadC_of_sliceRC_any_P6AN4` 把它包成 C11SH 形的 T1 ⇒ T0（INTEGRATION-ONLY）⇒ final 支
  `hbcadC` 的 "final-slab 版 P6L3 孪生" 树内**已有**，final 支缺的只是 T1 本身。

**T1 producer 链（event 支，现状）**：`shallowSliceRC_of_ksw_short_C11KS`（K-SW ⇐ KSW2
`ksw_pos_C11KS2`）→ PICKT1 `shallowSliceRC_of_pickedCenter_C11PT`（U 侧 `hUVC` ⇐ 合同族
`hPC : PickedCenterNeighborhood_C11PT`）→ HBCADC `hbcadC_of_pickedCenter_P6BC`（22:1x 在跑，event 支
装配）。event 支 hbcadC 的**精确剩余 binder**：
1. T1 late-K 组：`recordsF / hHI(a₀) / hcanK / hδF / hacc / hrad / hord /
   hscaleK((n+1)·max(n+1, Q) ≤ scale) / hbirthA / hpinchK0(∩ Ici T₀) / hslabK /
   hqR(max(n+1, Q) ≤ R) / hT₀`；其中 `hslabK`（`EventSlabsDerivative Ctime Q`）是全域导数背景
   = J10GEN 迁移义务；
2. seed K0：`Tn aSeed seedTrace L hL hwin`、`ρV hρV`；
3. `hdistQC`（traced-conditioned、余量 `L/4`、跨 stage 的 seed closure）：owner HDISTC
   `hdistC_of_traced_anySeed_C11G3`（`L ↦ L/4`），**不是** `hdistW`；
4. `hPC`（`PickedCenterNeighborhood_C11PT` 族）⇐
   (a) StepOne slice 部分 ⇐ hgood + `hdistQC` + 三角不等式（PICKT1 HANDOVER 1，接线可证）；
   (b) **`PickedCenterWindowSeed_C11PT`**（中心尺度窗口 seed closure）= 真缺口：SEEDCL2
   `windowScal_of_pickedTop_local_C11SC2` 只给路线 (i) 的**归纳步**（slice 界 ⇒ 窗口 closure），
   base case（first-failure / continuity）缺；路线 (ii)（变尺度窗口改 ShortSLT / KSW2 核）待
   R-C11-18；
   (c) κ 字段 ⇐ PBKAPPA FRESH 中心版。

**final 支**：T1 ⇒ T0 由本文件付；T1 producer **缺**：T1 壳 `hsliceR_lateHI_core_short_C11KS` /
`hsliceR_lateHI_core_pickedCenter_C11PT` 要 `htj : t n < time (j n).succ`（σ 在 event slab），
final σ 的窗口切片 `activeStage v = last` 不被 `j′ : Fin eventCount` 覆盖。repair target：final-slab
T1 壳（K-SW 在 final slab 的切片；ShortSLT 用 extendAt final 构形 `H := prefixAt last`、
`G := finalSlab.restrictIncoming`——`ShortSLT_C11KS` 对 `(H, G)` 通用，与本车道 G2 的 final
`TopAnchorInputs` 同一构形），owner HBCADC 续 / KSW。

**与 G1 hseedTop 的关系**：`hbcadC` 只在严格负偏移切片（`σ′ < 0`、`σ₂ < 0`）消费数据；hseedTop
在 top（`σ₂ = 0`）。两者不互相循环；共同上游是中心 / top 尺度的窗口 seed closure（base case 缺，
见 G1 文件头与上面 4(b)）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **T1 ⇒ T0，任意 σ（`_P6AN4`，INTEGRATION-ONLY）**：= P6FC
`hbcadC_of_slice_dichotomy_open_final_P6FC`（定义展开），
写成 SHALLOW C11SH 合同形：`ShallowSliceRC_C11SH η₃ Lc Kh σ y R ⇒ ShallowBcadC_C11SH Kh σ y R`
（`Kh = (K ·).toHistory`），**无** P6L3 的 `σ n < time last` 前提 ⇒ final slab 的 σ 亦适用。 -/
theorem shallowBcadC_of_sliceRC_any_P6AN4 :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R →
      ObservedHistory.ShallowBcadC_C11SH (fun n => (K n).toHistory) σ y R :=
  ObservedHistory.hbcadC_of_slice_dichotomy_open_final_P6FC.{u}

/-- consumer（G3，`_P6AN4`）：final 构形（`time last < σ`）下 T1 ⇒ T0 可用——P6L3 版因 `σ < time last` 不适用，
本定理无此前提。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    (_ : ∀ n, (K n).time (Fin.last (K n).eventCount) < σ n) (hR : ∀ n, 0 < R n)
    (hR1 : ∀ᶠ n in atTop, 1 ≤ R n) :
    ∃ η₃ Lc : ℝ, 0 < η₃ ∧ 0 < Lc ∧
      (ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R →
        ObservedHistory.ShallowBcadC_C11SH (fun n => (K n).toHistory) σ y R) := by
  obtain ⟨η₃, _, Lc, hη₃, _, hLc, h⟩ := shallowBcadC_of_sliceRC_any_P6AN4.{u}
  exact ⟨η₃, Lc, hη₃, hLc, h K σ y R hR hR1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
