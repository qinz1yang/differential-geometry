import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowT1FinalCoreP6TF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowPointPickC11PT

/-!
# SHALLOW T1 壳的 final 孪生：driver 中心邻域合同 final 形付 U 侧（O-CH11-T1FINAL G1，后缀 `_P6TF` / `_C11PT1`）

PICKT1 `hsliceR_lateHI_core_pickedCenter_C11PT`（event 支）要 `htj : t n < time (j n).succ`：唯一用它的步是
C11KS 壳 `hsliceR_lateHI_core_short_C11KS` 的 `hlast`（⇒ `activeStage v ≠ last` ⇒ 切片 `v` 在
event slab `j′`，
喂 `KSW_C11KS` event 单切片 + U 侧 event 块）。ANCHOR final 构形 `time last < t n` 下切片可落在 final slab
（`activeStage v = last`），不被 `j′ : Fin eventCount` 覆盖（HBCADC final 支 BLOCKED 的原因）。本文件 = final 孪生：
* 合同 **`PickedCenterNeighborhood_final_C11PT1`**（PROVISIONAL[合同]）：PICKT1 event 合同 ∧ final slab 块（与
  ANCHOR4 G2 `PickedBallShortWindow_final_P6AN4` 同型：度量 = final slab incoming `GF`（T1 里由 `hG` 钉成
  `(K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl`），窗口 `v′ ∈ (time last, v)`，κ 于
  `τ ∈ [v − θ/Rn, v] ∩ (time last, horizon)`）。同 event 合同：**不含曲率上界**。
* `kswHUF_of_pickedCenter_final_C11PT1`（PROVED）：final slab 块逐点付 final 单切片的 U 侧
  （`kswHU_of_pickedCenter_C11PT` 的 final 孪生：球包含 + 窗口包含）；
  `pickedCenterNeighborhood_mono_C11PT1` / `…_final_mono_C11PT1`（PROVED）：
  合同窗口对 `θ` 单调（短窗核取 `θ := min θ₀ (1/2) ≤ θ₀`）。
* **`hsliceR_lateHI_core_pickedCenter_final_P6TF`**（PROVISIONAL[合同 final 形]）：T1 壳结论的 final 版**逐字**
  （与 `hsliceR_lateHI_core_pickedCenter_C11PT` 结论只差合同 antecedent：`PickedCenterNeighborhood_C11PT …` ↦
  `PickedCenterNeighborhood_final_C11PT1 … (G n) …`）。证明 = 短窗 final 核心
  `hsliceR_lateHI_core_final_short_P6TF`
  （单切片 = `slice_dichotomy_short_both_P6TF`，K-SW 两合取项由 `shortSLT_C11KS2` PROVED 付）+ 两块 payment。
* consumer **`shallowSliceRC_of_pickedCenter_final_P6TF`**：T1 条件形 `ShallowSliceRC_C11SH`
  （PICKT1 consumer 的
  final 孪生，`hPC ↦ hPCF`，`hdistQC` 同原壳）。

**binder 改动（相对 PICKT1 event 壳）**：删 `j t htj hσ`（σ 位置无关：`σ` 在 event slab 时 final 分支空转）；加
`hfin G hG hpinchF hderF`（与 P6HF final 核心 `hsliceR_lateHI_core_final_P6HF` 同名同形）。
* `hderF : (G n).DerivativeBoundBefore Ctime (Q n) horizon` = `hslabK` 的 final slab 孪生（全域导数背景，
  **J10GEN 迁移类**，与 AN4 final 链 `hderG` 同族）；
* `hpinchF : PhiAlmostNonnegative (G n).flow (Ico (time last) horizon ∩ Ici (T₀ n)) phi` =
  `hpinchK0` 的 final 孪生，
  与 AN4 final 链 `hpinch` 第二合取项**同形**（FINCOND 层 supply）。它**不是** J10GEN 的 `hpinX`：`hpinX` 是沿 history
  的 Hamilton–Ivey 区域 `InFixedHamiltonIveyRegion (stageMetric …) (a₀X + τ)`（逐点 HI 传播，J10 ceiling 用），
  `hpinchF` 是 final slab 上 `T₀` 之后的 φ-almost-nonnegative；二者共同上游 = HI 传播（Hamilton–Ivey ⇒ admissible
  `phi` 下 φ-pinching），但槽不同、不能互代。

**为何不需要 top ceiling（CXJF2 `exists_extendAt_ceiling_CXJF2` / CXUT
`exists_top_ceiling_general_CXUT`）**：T1 只在
严格负偏移切片消费数据：`σ₂ < 0` ⇒ `v ≤ σ + σ₂/R < σ ≤ horizon`（`σ n ∈ Icc 0 horizon`），故 final 单切片的
`v < horizon`（ShortSLT 的 `t < s`，`s := horizon`）免费成立；`σ = horizon` 的 top 点只出现在
`hseedTop`（ANCHOR4 G1，
`σ₂ = 0`），不在 `hbcadC` / T1 的消费面。ceiling 是 hsurvive / hstop 侧的工具，T1 壳不用。

非循环：前提中无 `hdistW` / `HU_` / `hgapJ` / `hclosG` / `hscalU` / `CanonicalLateCore` / `hspine`；合同不含曲率上界
（不是 BCBD，不与 T1 结论循环）。审计做传递依赖名字扫描。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section Contract

/-- **中心邻域合同 final 形（`_C11PT1`，PROVISIONAL[合同]；owner = driver 中心选点 / PICKSEL）**：
PICKT1 event 合同 `PickedCenterNeighborhood_C11PT` ∧ **final slab 块**（ANCHOR4 G2
`PickedBallShortWindow_final_P6AN4` 同型）：对 final slab 内的 slice 时刻 `v ∈ (time last, horizon)`、
`v ∈ [σ − Tc/Rn, σ]`、`x₁ ∈ B_σ(y, Dw/√Rn)` 的 backward trace `tr`（起点 stage `last`）、
`x ∈ B_v(tr x₁, Dc/√Rn)`（度量 = final slab incoming `GF`）：
(1) `R(v, x) > qthr` ⇒ spatial canonical witness（neck chart）；
(2) 窗口 `v′ ∈ (time last, v)`、`v − θ/Rn ≤ v′`、`R(v′, x) > qthr` ⇒ `|∇R| ≤ Cgrad R^{3/2}`；
(3) `τ ∈ [v − θ/Rn, v] ∩ (time last, horizon)` 处半径 `b ≤ ρ` 的 parabolically controlled ball
κ-noncollapsed。
`GF` 的实例 = `(K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl`（T1 定理由 `hG` 钉死）。
**不含曲率上界**（同 event 合同）。 -/
def PickedCenterNeighborhood_final_C11PT1 (Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u})
    (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier) : Prop :=
  PickedCenterNeighborhood_C11PT Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y ∧
  ∀ v : ℝ, K.time (Fin.last K.eventCount) < v → v < K.horizon →
    (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
  ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn),
  ∀ (hjσ : Fin.last K.eventCount ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory (Fin.last K.eventCount) (K.toHistory.activeStage σ) hjσ
      x₁),
  ∀ x ∈ riemannianBallOf (GF.flow.base.metric v) (tr.point (Fin.last K.eventCount) le_rfl hjσ)
      (Dc / Real.sqrt Rn),
    (qthr < GF.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness (GF.flow.base.metric v) ε C1 C2 x,
        W.capTubeHasNeckChart ε) ∧
    (∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v, v - θ / Rn ≤ v' →
      qthr < GF.flow.scalar v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential GF.flow v' x ξ| ≤
          Cgrad * GF.flow.scalar v' x * Real.sqrt (GF.flow.scalar v' x) *
            Real.sqrt ((GF.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ / Rn ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz x →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))

/-- **inhabitant（`_C11PT1`）**：`Dc = 0` 时两块的邻域球都空，合同平凡成立（定义一致性检查）。 -/
theorem pickedCenterNeighborhood_final_zero_C11PT1 (Dw Tc θ Rn qthr ρ κ ε C1 C2 : ℝ)
    (Cgrad : ℝ≥0) (K : RetainedCoreHistory.{u})
    (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier) :
    PickedCenterNeighborhood_final_C11PT1 Dw 0 Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K GF σ y := by
  refine ⟨pickedCenterNeighborhood_zero_C11PT Dw Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y, ?_⟩
  intro v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf (GF.flow.base.metric v)
      (tr.point (Fin.last K.eventCount) le_rfl hjσ) x < ENNReal.ofReal (0 / Real.sqrt Rn) := hx
  rw [zero_div, ENNReal.ofReal_zero] at hx'
  exact ENNReal.not_lt_zero hx'

/-- **event 合同对窗口单调（`_C11PT1`，PROVED）**：`θ′ ≤ θ`、`0 < Rn` ⇒ 合同（窗口 `θ`）⇒ 合同（窗口 `θ′`）。 -/
theorem pickedCenterNeighborhood_mono_C11PT1 {Dw Dc Tc θ θ' Rn qthr ρ κ ε C1 C2 : ℝ}
    {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ : θ' ≤ θ) (hRn : 0 < Rn)
    (h : PickedCenterNeighborhood_C11PT Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y) :
    PickedCenterNeighborhood_C11PT Dw Dc Tc θ' Rn qthr ρ κ ε C1 C2 Cgrad K σ y := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  obtain ⟨h1, h2, h3⟩ := h j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  have hd : θ' / Rn ≤ θ / Rn := div_le_div_of_nonneg_right hθ hRn.le
  exact ⟨h1, fun v' hv' hle => h2 v' hv' (by linarith), fun τ hτ => h3 τ (by linarith)⟩

/-- **final 合同对窗口单调（`_C11PT1`，PROVED）**：两块都只在窗口下界用 `θ`。 -/
theorem pickedCenterNeighborhood_final_mono_C11PT1 {Dw Dc Tc θ θ' Rn qthr ρ κ ε C1 C2 : ℝ}
    {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}}
    {GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon}
    {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ : θ' ≤ θ) (hRn : 0 < Rn)
    (h : PickedCenterNeighborhood_final_C11PT1 Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K GF σ y) :
    PickedCenterNeighborhood_final_C11PT1 Dw Dc Tc θ' Rn qthr ρ κ ε C1 C2 Cgrad K GF σ y := by
  refine ⟨pickedCenterNeighborhood_mono_C11PT1 hθ hRn h.1, ?_⟩
  intro v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  obtain ⟨h1, h2, h3⟩ := h.2 v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  have hd : θ' / Rn ≤ θ / Rn := div_le_div_of_nonneg_right hθ hRn.le
  exact ⟨h1, fun v' hv' hle => h2 v' hv' (by linarith), fun τ hτ => h3 τ (by linarith)⟩

end Contract

section Payment

/-- **final slab 块逐点付 final 单切片的 U 侧（`_C11PT1`，PROVED）**：`kswHU_of_pickedCenter_C11PT` 的 final 孪生。
合同 final 形（`Dc = Dd + Rad`、`qthr = Cg·Rn`、窗口 `θ₀`）⇒ 合格 `w`（`d_v(tr x₁, w) < Dd/√Rn`、
`Rn ≤ q := R_GF(v, w)`）处 final 块三项（半径 `Rad`、窗口 `v − θ₀/q`、阈值 `Cg·Rn`、κ 半径 `ρ`）。
证明 = 球包含 `B_v(w, Rad/√q) ⊆ B_v(tr x₁, (Dd+Rad)/√Rn)` + 窗口包含 `θ₀/q ≤ θ₀/Rn`。 -/
theorem kswHUF_of_pickedCenter_final_C11PT1 {Dw Dd Rad Tc θ₀ Rn Cg ρ κ ε C1 C2 : ℝ}
    {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}}
    {GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon}
    {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ₀ : 0 ≤ θ₀) (hRn : 0 < Rn)
    (hPC : PickedCenterNeighborhood_final_C11PT1 Dw (Dd + Rad) Tc θ₀ Rn (Cg * Rn) ρ κ ε C1 C2
      Cgrad K GF σ y)
    (v : ℝ) (hv1 : K.time (Fin.last K.eventCount) < v) (hv2 : v < K.horizon)
    (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : Fin.last K.eventCount ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory (Fin.last K.eventCount) (K.toHistory.activeStage σ) hjσ
      x₁)
    (w : (K.stage (Fin.last K.eventCount)).Carrier)
    (hzw : riemannianEDistOf (GF.flow.base.metric v)
      (tr.point (Fin.last K.eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn))
    (hRw : Rn ≤ GF.flow.scalar v w) :
    (∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w (Rad / Real.sqrt (GF.flow.scalar v w)),
      Cg * Rn < GF.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness (GF.flow.base.metric v) ε C1 C2 x,
        W.capTubeHasNeckChart ε) ∧
    (∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w (Rad / Real.sqrt (GF.flow.scalar v w)),
      ∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v,
      v - θ₀ / GF.flow.scalar v w ≤ v' →
      Cg * Rn < GF.flow.scalar v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential GF.flow v' x ξ| ≤
          Cgrad * GF.flow.scalar v' x * Real.sqrt (GF.flow.scalar v' x) *
            Real.sqrt ((GF.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ₀ / GF.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ z ∈ riemannianBallOf (GF.flow.base.metric v) w (Rad / Real.sqrt (GF.flow.scalar v w)),
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) := by
  have hθq : θ₀ / GF.flow.scalar v w ≤ θ₀ / Rn := div_le_div_of_nonneg_left hθ₀ hRn hRw
  have hsub : ∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w
      (Rad / Real.sqrt (GF.flow.scalar v w)),
      x ∈ riemannianBallOf (GF.flow.base.metric v)
        (tr.point (Fin.last K.eventCount) le_rfl hjσ) ((Dd + Rad) / Real.sqrt Rn) := by
    intro x hx
    have hx' : riemannianEDistOf (GF.flow.base.metric v) w x <
        ENNReal.ofReal (Rad / Real.sqrt (GF.flow.scalar v w)) := hx
    have hRad : 0 < Rad / Real.sqrt (GF.flow.scalar v w) :=
      ENNReal.ofReal_pos.mp (zero_le.trans_lt hx')
    have hRad0 : 0 ≤ Rad := by
      by_contra hneg
      have : Rad / Real.sqrt (GF.flow.scalar v w) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (Real.sqrt_nonneg _)
      linarith
    have hDd : 0 < Dd / Real.sqrt Rn := ENNReal.ofReal_pos.mp (zero_le.trans_lt hzw)
    have hRq : Rad / Real.sqrt (GF.flow.scalar v w) ≤ Rad / Real.sqrt Rn :=
      div_le_div_of_nonneg_left hRad0 (Real.sqrt_pos.2 hRn) (Real.sqrt_le_sqrt hRw)
    change riemannianEDistOf (GF.flow.base.metric v)
      (tr.point (Fin.last K.eventCount) le_rfl hjσ) x < ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn)
    calc riemannianEDistOf (GF.flow.base.metric v)
          (tr.point (Fin.last K.eventCount) le_rfl hjσ) x
        ≤ riemannianEDistOf (GF.flow.base.metric v)
            (tr.point (Fin.last K.eventCount) le_rfl hjσ) w +
          riemannianEDistOf (GF.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Dd / Real.sqrt Rn) + ENNReal.ofReal (Rad / Real.sqrt Rn) :=
          ENNReal.add_lt_add hzw (hx'.trans_le (ENNReal.ofReal_le_ofReal hRq))
      _ = ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn) := by
          rw [← ENNReal.ofReal_add hDd.le (hRad.le.trans hRq), add_div]
  refine ⟨fun x hx hC => (hPC.2 v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).1 hC,
    fun x hx v' hv' hθ' hC => (hPC.2 v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).2.1 v' hv'
      (by linarith) hC,
    fun τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hctl =>
      (hPC.2 v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr z (hsub z hz)).2.2 τ (by linarith) hτ2 hτ3 hτ4 zz
        hzz b hb hbρ hctl⟩

end Payment

section T1

/-- **T1 核心形 final 孪生 ⇐ 中心邻域合同 final 形（`_P6TF`，PROVISIONAL[合同
`PickedCenterNeighborhood_final_C11PT1`]）**：`hsliceR_lateHI_core_pickedCenter_C11PT` 的结论**逐字**，只把合同
antecedent 换成 final 形（`… (K n) (G n) (σ n) (y n)`）；binder：删 `j t htj hσ`，加 `hfin G hG hpinchF hderF`
（P6HF final 核心同形）。σ 可在 final slab（`time last < σ ≤ horizon`）也可在 event slab。
证明：短窗 final 核心 `hsliceR_lateHI_core_final_short_P6TF`（取 `θ := min θ₀ (1/2)`；K-SW 两合取项 PROVED）；
event 块 ⇐ `kswHU_of_pickedCenter_C11PT`（合同第一分量经 `pickedCenterNeighborhood_mono_C11PT1` 缩到 `θ`），
final 块 ⇐ `kswHUF_of_pickedCenter_final_C11PT1`（合同 final 形经 `…_final_mono_C11PT1` 缩到 `θ`）。
final 切片 `v < horizon` 由 `σ₂ < 0` 得，不用 ceiling。 -/
theorem ObservedHistory.hsliceR_lateHI_core_pickedCenter_final_P6TF
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l, PickedCenterNeighborhood_final_C11PT1 Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n)
        (ρV n) κ ε C1 C2 Cgrad (K n) (G n) (σ n) (y n)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
              ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                w → ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric
                    ((K n).toHistory.activeStage v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage
                ((K n).toHistory.activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  have hθ : 0 < min θ₀ (1 / 2) := lt_min hθ₀ one_half_pos
  have hθle : min θ₀ (1 / 2) ≤ θ₀ := min_le_left _ _
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_final_short_P6TF (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
      hθ (min_le_right _ _) hεle hκ hphi hCg hη₃ hLc hfin hG recordsF hHI hcanK hδF hacc hrad
      hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos hqR hT₀ Tn aSeed haT hsT has
      pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hPC => ?_⟩
  refine hcore l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl ?_ ?_
  · filter_upwards [hPC] with n hn
    intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr _ _ w _ hzw hRw
    have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
    have hvT : (σ n : ℝ) - -σ₁ / R n ≤ v := by
      rw [neg_div, sub_neg_eq_add]
      exact hvσ1
    exact kswHU_of_pickedCenter_C11PT hθ.le (hRpos n)
      (pickedCenterNeighborhood_mono_C11PT1 hθle (hRpos n) hn.1) j' v hv1 hv2 hvT
      (by linarith) x₁ hx₁ hjσ tr w hzw hRw
  · filter_upwards [hPC] with n hn
    intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr _ _ w _ hzw hRw
    have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
    have hvT : (σ n : ℝ) - -σ₁ / R n ≤ v := by
      rw [neg_div, sub_neg_eq_add]
      exact hvσ1
    exact kswHUF_of_pickedCenter_final_C11PT1 hθ.le (hRpos n)
      (pickedCenterNeighborhood_final_mono_C11PT1 hθle (hRpos n) hn) v hv1 hv2 hvT
      (by linarith) x₁ hx₁ hjσ tr w hzw hRw

/-- **SHALLOW T1 ⇐ 中心邻域合同 final 形（consumer，`_P6TF`，PROVISIONAL[合同族 `hPCF`]）**：
`shallowSliceRC_of_pickedCenter_C11PT` 的 final 孪生：`hPC ↦ hPCF`（量词前缀逐字：`Rad σ₁ σ₂ φ Dw Dd T Kc` +
traced-region 前提，合同换 final 形），binder 改动同核心形；证明 = 本文件核心形 + `hdistQC`（同原壳）。
结论 = `ShallowSliceRC_C11SH η₃ Lc (K ·).toHistory σ y R`。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedCenter_final_P6TF
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hPCF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_final_C11PT1 Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1
        C2 Cgrad (K n) (G n) (σ n) (y n)) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_pickedCenter_final_P6TF (C1 := C1) (C2 := C2)
      (Cgrad := Cgrad) hθ₀ hεle hκ hphi hCg hη₃ hLc hfin hG recordsF hHI hcanK hδF hacc hrad hord
      hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos hqR hT₀ Tn aSeed haT hsT has pT
      seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun φ hφ σ₁ σ₂ h12 hσ₂ Dw hDw T Kc hT hKc htr => ?_⟩
  refine hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw ?_
    (hPCF Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith

/-- consumer：合同 final 形的 inhabitant（`Dc = Dd + Rad = 0`）逐点付 final 块——`Rad = −Dd` 时 U 球为空，三项
平凡；检查 `kswHUF_of_pickedCenter_final_C11PT1` 与合同 final 形的接口对齐。 -/
example {Dw Dd Tc θ₀ Rn Cg ρ κ ε C1 C2 : ℝ} {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}}
    {GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon}
    {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ₀ : 0 ≤ θ₀) (hRn : 0 < Rn)
    (v : ℝ) (hv1 : K.time (Fin.last K.eventCount) < v) (hv2 : v < K.horizon)
    (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : Fin.last K.eventCount ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory (Fin.last K.eventCount) (K.toHistory.activeStage σ) hjσ
      x₁)
    (w : (K.stage (Fin.last K.eventCount)).Carrier)
    (hzw : riemannianEDistOf (GF.flow.base.metric v)
      (tr.point (Fin.last K.eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn))
    (hRw : Rn ≤ GF.flow.scalar v w) :=
  kswHUF_of_pickedCenter_final_C11PT1 (Rad := -Dd) (Cg := Cg) (ρ := ρ) (κ := κ) (ε := ε)
    (C1 := C1) (C2 := C2) (Cgrad := Cgrad) hθ₀ hRn
    (by
      have e : Dd + -Dd = 0 := by ring
      rw [e]
      exact pickedCenterNeighborhood_final_zero_C11PT1 Dw Tc θ₀ Rn (Cg * Rn) ρ κ ε C1 C2 Cgrad K
        GF σ y)
    v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr w hzw hRw

end T1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
