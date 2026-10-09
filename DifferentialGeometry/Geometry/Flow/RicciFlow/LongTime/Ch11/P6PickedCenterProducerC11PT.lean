import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowPointPickC11PT

/-!
# 中心邻域合同的 producer 合同（O-CH11-PICKT1 G2，后缀 `_C11PT`；只写合同，不证）

G1 合同 `PickedCenterNeighborhood_C11PT`（中心 `(σ_n, y_n)`、尺度 `R_n`、区域 `P_n`：slice 时刻
`v ∈ [σ − Tc/R_n, σ]`、`B_v(tr x₁, Dc/√R_n)`、窗口 `[v − θ/R_n, v]`）的 producer 拆成两块合同。

## 1. Perelman 12.1 Step 1 在 slice 内的精确陈述 = `PickedCenterStepOne_C11PT`
"从坏点出发反复取更坏的坏点，有限步后停在一个坏点 `(σ, y)`，它的 backward 区域里 `R ≥ Λ·R(y)` 的点都是好点"。
slice / trace 形：`P_n` 里（含窗口时刻 `v′`）`R(v′, z) ≥ Λ·R_n` 的点都有 `HasSpatialCanonicalTimeControl`
（spatial canonical witness + 时间导数界 `|∂_t R| ≤ Ctime R²`）。**它不含曲率上界**：停止条件是"没有更坏的**坏点**"，
不是 `R ≤ 4R(y)`（后者是 rescaled point picking 的曲率极大性，见 §3）。
[locator：沿用树内 `CanonicalTimeControlPointSelection` / `P6R2` / `EarlierGoodTraceLocal_P6N:173`（"KL 的
point-picking"）已登记的引用；本车道未逐页重核 KL §52 / Perelman I §12.1 原文。]

**树内已有（Step 1 本身已证）**：
* `exists_localized_canonical_time_control_point_selection`
  （`Surgery/Topology/CanonicalTimeControlPointSelection.lean:55`）：finite moving-seed selection，
单 history
  的迭代选点（曲率每步至少翻倍，`⌊K/R⌋₊` 计数终止）。
* `selection_of_bad_sequence_retained_P6R2`（`Ch11/P6SelectionRetainedP6R2.lean:103`）：序列版，输出坏中心
  `(σ_n, y_n)`、`R_n = R(σ_n, y_n)`、`L_n → ∞`、**hgood**：
`v ∈ [σ − L²/R, σ]`、`d_v(O_v, z) ≤ d_σ(O_σ, y) + L/√R`、
  `R(v, z) ≥ 4R_n` ⇒ `HasSpatialCanonicalTimeControl`。`Cg` 版 = `HgoodCg_C11SH`（SHALLOW）。
* ALPHA：`selection_of_bad_sequence_retained_half_C11AL`（L/2 余量版）、`hgood_secondScale_C11AL`（二次尺度
  `SecondScaleCg_C11SH`）。
⇒ T1 的 driver 中心**已经是** 12.1 Step 1 选出的点；(b) 不需要挪中心，冻结接口（`ShallowSliceRC_C11SH` 的
`σ y R`、GAPTOP6 / hgapJ）不用改，**不 BLOCKED 在接口上**。

`PickedCenterStepOne_C11PT` 与 hgood 的差别只有一处：hgood 的区域是 seed-distance Good 域（每个时刻量
`d_v(O_v, ·)`），`P_n` 是 trace 邻域 × 窗口。slice 时刻 `v` 上 `P_n ⊆` Good 域可由 `hdistQC`（traced 点
`L/4` 余量）+ 三角不等式（`Dc/√R_n ≤ (3L/4)/√R_n`，`L → ∞`）得到（可证接线，PICKBALL
`pickedBallWitness_of_hgood_C11PB` 的中心版）；**窗口时刻 `v′ < v` 上 `P_n ⊆` Good 域就是 §2 的缺口**。

## 2. 真缺口 = 中心尺度窗口 seed closure `PickedCenterWindowSeed_C11PT`
`x ∈ B_v(tr x₁, Dc/√R_n)`、`v′ ∈ [v − θ/R_n, v]`、`R(v′, x) > qthr` ⇒ `d_{v′}(O, x) ≤ D`
（`D = d_σ(O_σ, y) + L/√R_n`）。有了它：StepOne（窗口部分）⇐ hgood + 本合同；G1 的 witness / 梯度 ⇐ StepOne
（witness ⇒ 梯度走 PICKBALL G4 `pickedBallGrad_of_hgood_C11PB` 的 `C2 ≤ Cgrad` 机制）；
G1 的 κ ⇐ PBKAPPA FRESH 路线
（`pickedBallKappa_of_fresh_distortion_C11PK` 的中心版：footprint 也是同一个窗口距离畸变问题 + 端点 Ricci + `hdσ`）。
这就是 R-C11-15 Q4 [推断] 的 "picked-ball/chain first-exit closure"，现在只需在**一个中心尺度**上付一次。

## 3. 为什么不把 "`P_n` 内 `R ≤ Λ·R_n`" 当输入（lead 规格里的字段）
它确实是 SEEDCL 核 `seed_closure_firstExit_P6L4`（经 `windowScal_of_pickedTop_C11SC`）的 `hscal` 输入：有了它，
ODE（`Ctime·Λ·θ ≤ 1/2`）+ first-exit 直接给 §2。但 `R ≤ Λ·R_n` on `P_n`、`Λ ≤ QB`，会直接推出 T1 非 CWP 分支
在 `P_n` 内的结论（`R(w) ≥ R_n` ⇒ `R ≤ Λ R(w)`），也就是在中心尺度把目标写成 binder，与 lead 否掉 (a) 的理由相同。
曲率型选点（rescaled point picking：`R ≤ 4R(y′)` on `B(y′, A/√R(y′))`）会**挪中心**到 `y′`，`y′` 不再保证是坏点，
driver 的 `hbad` / hgood / 窗口前提都要重证 ⇒ 那条路要改冻结接口（`ShallowSliceRC_C11SH` 的 `σ y R` 来源），不采用。

## 4. §2 的两条可能 producer（[推断]，都未证）
(i) **时间方向 bootstrap**：在 `v` 上从下往上，用较早 slice 的 BCBD（T1 结论，常数 `QB`）+ 反向 ODE 给窗口曲率顶，
再用 first-exit 得到 §2，再经 KSW 得到 `v` 处 BCBD。缺 base case（`P_n` 最早 slice 的窗口），需要 continuity /
first-failure 论证；常数只需 `o(L²)` 增长（窗口距离漂移 `∫ √R ≲ √(M R_n)·θ/R_n` 对 `L/√R_n` 小即可）。
(ii) **变尺度窗口（改 ShortSLT 核，(c)）**：U 侧窗口按点自身尺度 `θ/R(v, x)` 取，而不是中心的共同 `θ/q`。
自身尺度窗口上，slice 时刻 witness 的时间导数界给 `R ≤ 2R(v, x)`，漂移 `≲ θ/√R(v,x) ≤ θ/√(Cg R_n)`，first-exit 自动成立，
不用曲率顶。代价是 KSW2 核的共同窗口 flow limit 要改成"爆点前区域上的 limit"（Perelman 12.1 Step 2 的原始形状）——
新分析，owner SHALLOW-TOOLS M1 / KSW 核；R-C11-12 Q2(d)"中心尺度预算不等于整个球的共同预算"指向同一个问题。

非循环：只 import G1（`P6ShallowPointPickC11PT`）；只有合同 + inhabitant，无证明；不经 hscalU / hclosG / hclosC /
hUVC 的 M4 生产链 / CanonicalLateCore / hspine。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section ProducerContracts

/-- **12.1 Step 1 slice 形（`_C11PT`，PROVISIONAL[合同]；producer = 树内 selection hgood + §2 窗口 closure）**：
中心 `(σ, y)`、尺度 `Rn`、区域 `P`（slice 时刻 `v ∈ [σ − Tc/Rn, σ]`、`x₁ ∈ B_σ(y, Dw/√Rn)` 的 trace `tr`、
`x ∈ B_v(tr x₁, Dc/√Rn)`、窗口时刻 `v′ ∈ [v − θ/Rn, v]`）里 `R(v′, x) ≥ Λ·Rn` 的点有
`HasSpatialCanonicalTimeControl eps C1 C2 Ctime`（"`P` 内没有更坏的坏点"）。**不含曲率上界。** -/
def PickedCenterStepOne_C11PT (Dw Dc Tc θ Rn Λ eps C1 C2 : ℝ) (Ctime : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier) : Prop :=
  ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
    (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
  ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn),
  ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
  ∀ (v' : Icc (0 : ℝ) K.toHistory.horizon), v - θ / Rn ≤ (v' : ℝ) → (v' : ℝ) ≤ v →
    K.time j'.castSucc < v' →
  ∀ z : (K.toHistory.stageAt v').Carrier, HEq z x →
    Λ * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v') v') z →
    K.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z

/-- **中心尺度窗口 seed closure（`_C11PT`，PROVISIONAL[合同]；真缺口，owner SHALLOW-TOOLS M1 / DIST）**：
区域 `P` 的点 `x`（slice 时刻 `v` 位置）在窗口时刻 `v′ ∈ (time j′⁻, v)`、`v − θ/Rn ≤ v′`、`R(v′, x) > qthr` 时
`d_{v′}(O j′, x) ≤ D`（`O j′` = seed 在 stage `j′⁻` 的位置；`D = d_σ(O_σ, y) + L/√Rn`）。
= SEEDCL `PickedBallWindowSeed_C11PB` 的中心版（一个中心尺度、共同窗口 `θ/Rn`）。 -/
def PickedCenterWindowSeed_C11PT (Dw Dc Tc θ Rn qthr : ℝ) (K : RetainedCoreHistory.{u})
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier)
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier) (D : ℝ≥0∞) : Prop :=
  ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
    (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
  ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn),
  ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
  ∀ v' ∈ Ioo (K.time j'.castSucc) v, v - θ / Rn ≤ v' →
    qthr < (K.toHistory.event j').incoming.flow.scalar v' x →
    riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v') (O j') x ≤ D

/-- **inhabitant（`_C11PT`）**：`Dc = 0` 时区域球空，Step 1 合同平凡成立。 -/
theorem pickedCenterStepOne_zero_C11PT (Dw Tc θ Rn Λ eps C1 C2 : ℝ) (Ctime : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier) :
    PickedCenterStepOne_C11PT Dw 0 Tc θ Rn Λ eps C1 C2 Ctime K σ y := by
  intro j' v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal (0 / Real.sqrt Rn) := hx
  rw [zero_div, ENNReal.ofReal_zero] at hx'
  exact ENNReal.not_lt_zero hx'

/-- **inhabitant（`_C11PT`）**：`Dc = 0` 时区域球空，窗口 seed closure 合同平凡成立。 -/
theorem pickedCenterWindowSeed_zero_C11PT (Dw Tc θ Rn qthr : ℝ) (K : RetainedCoreHistory.{u})
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (y : (K.toHistory.stageAt σ).Carrier)
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedCenterWindowSeed_C11PT Dw 0 Tc θ Rn qthr K σ y O D := by
  intro j' v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal (0 / Real.sqrt Rn) := hx
  rw [zero_div, ENNReal.ofReal_zero] at hx'
  exact ENNReal.not_lt_zero hx'

/-- consumer：三个合同（G1 中心邻域、Step 1、窗口 closure）用同一个区域参数化 `(Dw, Dc, Tc, θ, Rn)`；
`Dc = 0` 时三者同时成立（接口对齐检查）。 -/
example (Dw Tc θ Rn Λ qthr ρ κ eps C1 C2 : ℝ) (Ctime Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier)
    (O : ∀ j' : Fin K.eventCount, (K.stage j'.castSucc).Carrier) (D : ℝ≥0∞) :
    PickedCenterStepOne_C11PT Dw 0 Tc θ Rn Λ eps C1 C2 Ctime K σ y ∧
      PickedCenterWindowSeed_C11PT Dw 0 Tc θ Rn qthr K σ y O D ∧
      PickedCenterNeighborhood_C11PT Dw 0 Tc θ Rn qthr ρ κ eps C1 C2 Cgrad K σ y :=
  ⟨pickedCenterStepOne_zero_C11PT Dw Tc θ Rn Λ eps C1 C2 Ctime K σ y,
    pickedCenterWindowSeed_zero_C11PT Dw Tc θ Rn qthr K σ y O D,
    pickedCenterNeighborhood_zero_C11PT Dw Tc θ Rn qthr ρ κ eps C1 C2 Cgrad K σ y⟩

end ProducerContracts

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
