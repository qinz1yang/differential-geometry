import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWShortWindowC11KS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedOrCapWin_P6LL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceScalarControl_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowContractC11SH

/-!
# picked-ball / chain 短窗数据合同（O-CH11-PICKBALL，R-C11-12 D-6 / D-9(2)，后缀 `_C11PB`）

SHALLOW 的 I1（`SliceLocalization_C11SH`）只给切片局部化，I2（`SecondScaleSurvival_C11SH`）只给坏点 `w`
的**点存活**；ShortSLT / K-SW 需要的是二次选点 `(w, v, q := R(v, w))` 处**整个球**
`B_v(w, Rad/√q)` 在**共同窗口** `[v − β/q, v]` 上的数据。本文件登记该合同并证明树内能付的部分。

## 合同（slice 层，`K.event j` incoming flow，`time j⁻ < v < time j⁺`）
`PickedBallShortWindow_C11PB β Λ Rad qthr ρ κ ε C1 C2 Cgrad K j v w` :=
* `PickedBallTop_C11PB Λ Rad`（**hpick**）：`∀ x ∈ B_v(w, Rad/√q), R(v, x) ≤ Λ q`（二次选点球的曲率界）；
* `PickedBallWitnessGrad_C11PB β Rad qthr`（**hUside**）= `PickedBallWitness_C11PB`（球上 `R > qthr` 处
  spatial canonical witness）∧ `PickedBallGrad_C11PB`（`v′ ∈ (time j⁻, v)`、`v − β/q ≤ v′` 上
  `R(v′, x) > qthr` 处梯度界）；
* `PickedBallKappa_C11PB β Rad ρ κ`（**hκ**）：`τ ∈ [v − β/q, v] ∩ slab`、球上点的 controlled ball
  （半径 `≤ ρ`）κ-noncollapsed。
另：`PickedBallSurvivalOrCap_C11PB`（ObservedHistory 层）= 整球 backward traces 到 `t − β/R` 且
`|Rm| ≤ 8√3(1 + Φ1 + Φ0) Λ R`（`isTracedRegion`），**或** 中心点的 late `CapWindowPoint`（实际 records、
年龄 `θcap`、空间窗口 `Dcap`）；slice 层 `PickedBallSurvivalOrCapSlice_C11PB`（TP `htrace` 结论形）。

## 与 `ShortSLT_C11KS θ` 输入面（slice 包装 `slice_scalar_bound_of_not_capWindowPoint_short_C11KS`）逐项对照
| ShortSLT 输入 | 本合同供给 |
|---|---|
| `U ⊇ B(w, Rad/√q)` | `U := B(w, Rad′/√q)`，`Rad ≤ Rad′`（球单调） |
| `hW`（`R > q` 处 witness） | `PickedBallWitnessGrad.1`（`qthr := q`） |
| `hgrad`（窗口 `v − θ/q ≤ v′`） | `PickedBallWitnessGrad.2`（`θ ≤ β` 缩窗） |
| `hnc`（κ，`τ` 在窗口） | `PickedBallKappa`（`θ ≤ β` 缩窗） |
| `hslab / hderG`（导数） | 全局 `EventSlabsDerivative / DerivativeBoundBefore`（不属 picked-ball） |
| `hpinch`、records 组 | 全局（late records、窗口 pinching） |
| `hnot`（¬CWP θ） | 与 CWP(θ) 分情形（consumer 输出 `CWP ∨ 标量界`） |
| `htrace`（整链 backward traces） | **不是** SLT 输入：SLT-W 内部由 `hnot` 经 chain capture 产生 |
`PickedBallTop` 与 `SurvivalOrCap` 不进 SLT 输入面；它们是 hUside 的时间局部化（first-exit closure）所需的
曲率 / 存活输入（跨窗口距离畸变 `e^{C Λ β}`）。

## 预算（R-C11-12 D-5 / D-6）
中心尺度预算 `θ* = 1/(2 max(Ctime, 1))` 只沿中心 trace 给 `2q/3 ≤ R ≤ 2q`；整球（`R ≤ Λ q`）共同 ODE 窗须
`Ctime · Λ · β ≤ 1/2`，即 `β ≤ θ*/Λ`（`shrunk_budget_C11PB`）。`center_budget_vacuous_C11PB`：`Λ ≥ 2`、
`Ctime ≥ 1` 时中心预算对 `R(s) = Λ q` 的球点给出的倒数下界 `1/(Λq) − Ctime θ*/q ≤ 0`（空洞）。

## PROVED（standard axioms）
* `common_window_scalar_le_C11PB` / `shrunk_budget_C11PB` / `center_budget_vacuous_C11PB`（预算算术）；
* `RetainedCoreHistory.pickedBall_scalar_le_along_traces_C11PB`：球顶界 + 全局导数界 + Λ 缩短预算 ⇒
  沿所有既存 backward trace `R ≤ 2 Λ R`
  （`scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L`）；
* `RetainedCoreHistory.pickedBall_survivalOrCap_C11PB`：上式 +
  `exists_isTracedRegion_or_capWindowPoint_at_scale_win_P6LL`
  ⇒ `PickedBallSurvivalOrCap_C11PB`（整球存活 + Rm 界 ∨ 实际 cap）；`.mono_age`（`θcap ≤ θ′`）；
  slice 层 `pickedBall_survivalOrCap_slice_C11PB`：hpick（`PickedBallTop_C11PB Λ A`）+ event `j` 导数界
  ⇒ `PickedBallSurvivalOrCapSlice_C11PB`（TP `htrace` 结论形的整球存活 ∨ K-SW 形 late CWP）；
* **空间余量**：`pickedBallWitness_of_hgood_C11PB`：selection `HgoodCg_C11SH Cg` + 中心 `w` 的 Good(L/2)
  + `R_n ≤ R(v, w)` + `0 ≤ Rad ≤ L/2` ⇒ `PickedBallWitness_C11PB Rad (Cg·R_n)`（hUside 的 witness 半）；
  `pickedBallWitnessGrad_of_hgood_C11PB`：+ binder hgrad ⇒ hUside；
* 单调性 `.mono`（`β′ ≤ β`、`Rad′ ≤ Rad`、`qthr ≤ qthr′`、`ρ′ ≤ ρ`）与 `Rad = 0` inhabitants。
## consumer（PROVISIONAL：binder `ShortSLT_C11KS θ` / `KSW_C11KS θ₀`）
* `RetainedCoreHistory.capWindowPoint_or_scalar_bound_of_pickedBall_C11PB`：ShortSLT 输入面 ⇐ 合同；
* `kswHU_of_pickedBall_C11PB`：K-SW 的逐点 U 侧前提 `hU`（`Cg·R_n` 阈值、`θ₀` 窗）⇐ 合同；
* `ksw_of_pickedBall_C11PB`：`KSW_C11KS θ₀` 的陈述把 `hU` 换成 picked-ball 合同族（`θ₀ ≤ β`、`Rad′ ≥ Rad`）。
## PROVISIONAL binder 与 owner（精确命题 = 上述 def）
* **hpick** `PickedBallTop_C11PB Λ Rad`：二次选点（slice 内 `Rescaled point picking`，`Λ = 4`）——owner =
  selection / point-picking 车道（P6SEL / ALPHA 的二次尺度选点）。
* **hgrad** `PickedBallGrad_C11PB β Rad (Cg·R_n)`（hUside 的梯度半；witness 半已由 hgood 付）：
  窗口 `[v − β/q, v]` 上球点的梯度界。缺 (i) 窗口内球点 seed-distance 的 first-exit closure（hgood /
  `SecondScaleCg_C11SH` 只在 seed 域内给控制）与 (ii) canonical neighbourhood 梯度估计（hgood 的
  `HasSpatialCanonicalTimeControl` 不含梯度）——owner = SHALLOW-TOOLS M1 / DIST（`FirstExitDistanceP6M4`
  路线，输入 = 本文件 `SurvivalOrCap` 的 Rm 界）+ canonical 梯度车道。
* **hκ** `PickedBallKappa_C11PB β Rad ρ κ`：κ footprint 覆盖实际 controlled balls（同一背景 κ）——owner =
  KAPPA / HFOOT（D-9(3)）。
* 类型桥已做：`pickedBall_survivalOrCap_slice_C11PB`（slice 层，`activeStage ⟨v, _⟩ = j⁻`，
  `activeStage_eq_castSucc_C11PB`）把 ObservedHistory 层结论搬到合同所在的 `K.event j` 形。
非循环：只 import KSW（LS3）、`TracedOrCapWin_P6LL`、`BackwardTraceScalarControl_P6L`；不经 hscalU / hclosG /
hclosC / hUVC / CanonicalLateCore / hspine（审计做传递依赖名字扫描）。不声称闭合。
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

section Budget

/-- **共同窗口 ODE 算术（`_C11PB`）**：球点 `R(s) ≤ Λ q`，倒数 ODE 下界 `1/R(s) − Ct·d ≤ 1/R(v)`，
`0 ≤ d ≤ β/q`，`Ct · Λ · β ≤ 1/2` ⇒ `R(v) ≤ 2 Λ q`。预算是 `β ≤ 1/(2 Ct Λ)`（按 `Λ` 缩短）。 -/
theorem common_window_scalar_le_C11PB {Ct Λ q Rs Rv d β : ℝ} (hq : 0 < q) (hRs : 0 < Rs)
    (hRv : 0 < Rv) (hRsΛ : Rs ≤ Λ * q) (hrec : 1 / Rs - Ct * d ≤ 1 / Rv) (hd : d ≤ β / q)
    (hCt : 0 ≤ Ct) (hbud : Ct * Λ * β ≤ 1 / 2) : Rv ≤ 2 * (Λ * q) := by
  have hΛq : 0 < Λ * q := hRs.trans_le hRsΛ
  have hΛ : 0 < Λ := (pos_iff_pos_of_mul_pos hΛq).mpr hq
  have hq0 : q ≠ 0 := hq.ne'
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have h1 : 1 / (Λ * q) ≤ 1 / Rs := one_div_le_one_div_of_le hRs hRsΛ
  have h2 : Ct * d ≤ 1 / (2 * (Λ * q)) := by
    have e1 : Ct * (β / q) = Ct * Λ * β / (Λ * q) := by field_simp
    have e2 : 1 / 2 / (Λ * q) = 1 / (2 * (Λ * q)) := by rw [div_div]
    calc Ct * d ≤ Ct * (β / q) := mul_le_mul_of_nonneg_left hd hCt
      _ = Ct * Λ * β / (Λ * q) := e1
      _ ≤ 1 / 2 / (Λ * q) := div_le_div_of_nonneg_right hbud hΛq.le
      _ = 1 / (2 * (Λ * q)) := e2
  have h3 : 1 / (Λ * q) = 2 * (1 / (2 * (Λ * q))) := by field_simp
  have h4 : 1 / (2 * (Λ * q)) ≤ 1 / Rv := by linarith
  exact (one_div_le_one_div (by positivity) hRv).mp h4

/-- **Λ 缩短的共同预算（`_C11PB`）**：`β := θ*/Λ`（`θ* = 1/(2 max(Ct, 1))`）满足 `Ct · Λ · β ≤ 1/2`。 -/
theorem shrunk_budget_C11PB {Ct Λ : ℝ} (hΛ : 0 < Λ) :
    Ct * Λ * (1 / (2 * max Ct 1) / Λ) ≤ 1 / 2 := by
  have hm : 0 < max Ct 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hm0 : max Ct 1 ≠ 0 := hm.ne'
  have e : Ct * Λ * (1 / (2 * max Ct 1) / Λ) = Ct / (2 * max Ct 1) := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith [le_max_left Ct 1]

/-- **中心预算不是整球预算（`_C11PB`）**：`Ct ≥ 1`、`Λ ≥ 2` 时，中心窗 `θ*/q`（`θ* = 1/(2 max(Ct, 1))`）
对 `R(s) = Λ q` 的球点只给出空洞的倒数下界 `1/(Λ q) − Ct · θ*/q ≤ 0`。 -/
theorem center_budget_vacuous_C11PB {Ct Λ q : ℝ} (hCt : 1 ≤ Ct) (hΛ : 2 ≤ Λ) (hq : 0 < q) :
    1 / (Λ * q) - Ct * (1 / (2 * max Ct 1) / q) ≤ 0 := by
  rw [max_eq_left hCt]
  have hCt0 : Ct ≠ 0 := (lt_of_lt_of_le one_pos hCt).ne'
  have hq0 : q ≠ 0 := hq.ne'
  have e : Ct * (1 / (2 * Ct) / q) = 1 / (2 * q) := by field_simp
  have h2 : 1 / (Λ * q) ≤ 1 / (2 * q) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hΛ hq.le)
  rw [e]
  linarith

end Budget

section SurvivalOrCap

open DifferentialGeometry.Geometry.Metric

/-- **球顶曲率界（ObservedHistory 层，`_C11PB`；hpick 的 `activeStage` 形）**：
`∀ x ∈ B_t(y, A/√R), R(t, x) ≤ Λ R`。 -/
def PickedBallTopObs_C11PB (H : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) H.toHistory.horizon)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (R A Λ : ℝ) : Prop :=
  ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y
      (A / Real.sqrt R),
    metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ Λ * R

/-- **整球存活或实际 cap（`_C11PB`，ObservedHistory 层）**：`B_t(y, A/√R)` 的每点有 backward trace 到
`t − β/R` 且 `|Rm| ≤ 8√3(1 + Φ1 + Φ0) Λ R`（`isTracedRegion`），或 `y` 是 late `CapWindowPoint`（实际
`records`、空间窗口 `‖x‖ < Dcap + 1`、年龄 `t − time j⁺ ≤ θcap / scale`）。 -/
def PickedBallSurvivalOrCap_C11PB (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (phi : ℝ → ℝ) (t : Icc (0 : ℝ) H.toHistory.horizon)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (R A β Λ Dcap θcap : ℝ) :
    Prop :=
  H.toHistory.isTracedRegion t y (A / Real.sqrt R) (β / R)
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Λ * R)) ∨
    ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ)
      (hl : j.succ ≤ H.toHistory.activeStage t)
      (B : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹

/-- **cap 年龄单调（`_C11PB`）**：`θcap ≤ θ′` ⇒ `SurvivalOrCap θcap ⇒ SurvivalOrCap θ′`（`neck.scale > 0`）。
例：`θcap ≤ θ₀ ≤ 1/2` 时送入 K-SW 的 CWP(θ₀) 消费面。 -/
theorem PickedBallSurvivalOrCap_C11PB.mono_age {H : RetainedCoreHistory.{u}}
    {p : CutoffParameters} {T₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p}
    {phi : ℝ → ℝ} {t : Icc (0 : ℝ) H.toHistory.horizon}
    {y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier} {R A β Λ Dcap θcap θ' : ℝ}
    (hθ : θcap ≤ θ') (h : PickedBallSurvivalOrCap_C11PB H records phi t y R A β Λ Dcap θcap) :
    PickedBallSurvivalOrCap_C11PB H records phi t y R A β Λ Dcap θ' := by
  rcases h with htr | ⟨j, hj, hl, B, b, x, hx, hxn, hage⟩
  · exact Or.inl htr
  · refine Or.inr ⟨j, hj, hl, B, b, x, hx, hxn, hage.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hθ
      (inv_nonneg.mpr ((records j hj).static b).neck.scale_pos.le)

/-- **球顶界 ⇒ 沿既存 traces 的共同窗口标量界（`_C11PB`，PROVED）**：球 `B_t(y, A/√R)` 上
`R(t, ·) ≤ Λ R`、全局导数界（阈值 `qcan ≤ Λ R`）、`u = t − β/R`、**`C · Λ · β ≤ 1/2`**（Λ 缩短的预算）⇒
球点的任何 backward trace（起点 `w ≥ u`）在 `[w, t]` 上 `R ≤ 2 (Λ R)`。= `TracedOrCapWin` 的 `hscal`。 -/
theorem RetainedCoreHistory.pickedBall_scalar_le_along_traces_C11PB (H : RetainedCoreHistory.{u})
    {C : ℝ≥0} {qcan : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hslabs : H.EventSlabsDerivative C qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C qcan t)
    {y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier} {R A β Λ : ℝ} (hR : 0 < R)
    (hΛR : 0 < Λ * R) (hqcan : qcan ≤ Λ * R) (hu : (u : ℝ) = t - β / R)
    (hbud : (C : ℝ) * Λ * β ≤ 1 / 2) (htop : PickedBallTopObs_C11PB H t y R A Λ) :
    ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y
        (A / Real.sqrt R),
      ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
        (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
        (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Λ * R) := by
  intro x hx w huw hwt B v hwv hvt
  have huw' : (u : ℝ) ≤ w := huw
  have htw : (t : ℝ) - w ≤ β / R := by linarith
  have hR0 : R ≠ 0 := hR.ne'
  have e : (C : ℝ) * (Λ * R) * (β / R) = C * Λ * β := by field_simp
  have htime : (C : ℝ) * (Λ * R) * ((t : ℝ) - w) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left htw (mul_nonneg C.coe_nonneg hΛR.le)
    linarith
  exact RetainedCoreHistory.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L H hwt
    B (fun i _ hl v hv hRv => hslabs i (i.castSucc_lt_succ.trans_le hl) _ v hv hRv)
    (fun j y hj _ v hv hRv => hcurrent j hj y v hv hRv)
    (fun h y ht _ v hv hRv => hfinal h ht y v hv hRv) hΛR hqcan (htop x hx) htime v hwv hvt

/-- **picked-ball 整球存活或实际 cap（`_C11PB`，PROVED）**：
`exists_isTracedRegion_or_capWindowPoint_at_scale_win_P6LL`
的常数前缀逐字；其 `hscal`（沿 traces `R ≤ 2 Q R`）换成**球顶界** `PickedBallTopObs_C11PB` + Λ 缩短预算
`C · Λ · β ≤ 1/2`（`Q := Λ`、`T := β`）。结论 `PickedBallSurvivalOrCap_C11PB`：整球 backward traces 到
`t − β/R` 且 Rm 界，或中心 late CWP（records / 年龄 `θcap ∈ [1/4, Θ)` / 空间窗口 `Dcap`）。 -/
theorem RetainedCoreHistory.pickedBall_survivalOrCap_C11PB :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ Dstar : ℝ, StandardCap.transitionEnd < Dstar →
    ∃ Rrad : ℝ, Dstar + 1 < Rrad ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale) →
      (∀ i hi b, 1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici T₀) phi) →
    ∀ u t : Icc (0 : ℝ) H.toHistory.horizon, u ≤ t → T₀ ≤ (u : ℝ) →
      (H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici T₀) phi) →
      H.EventSlabsDerivative C qcan (H.toHistory.activeStage t) →
      (∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
        (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t) →
      (∀ h : H.time (Fin.last H.eventCount) < H.horizon,
        H.toHistory.activeStage t = Fin.last H.eventCount →
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C qcan t) →
    ∀ (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (R A β Λ Dcap θcap : ℝ),
      0 < R → 0 < A → 0 < β → 1 ≤ Λ * R → (u : ℝ) = t - β / R →
      1 / 4 ≤ θcap → 1 - c / (8 * β * Λ) ≤ θcap → θcap < Θ → Dcap ≤ Dstar →
      qcan ≤ Λ * R → (C : ℝ) * Λ * β ≤ 1 / 2 → PickedBallTopObs_C11PB H t y R A Λ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * Λ) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Λ * β) * A < Dcap →
      PickedBallSurvivalOrCap_C11PB H records phi t y R A β Λ Dcap θcap := by
  obtain ⟨c, hc, hD⟩ :=
    RetainedCoreHistory.exists_isTracedRegion_or_capWindowPoint_at_scale_win_P6LL.{u}
  refine ⟨c, hc, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨Cbirth, hCb, hD⟩ := hD Θ hΘ hΘ1 C
  refine ⟨Cbirth, hCb, fun Dstar hDs => ?_⟩
  obtain ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, hD⟩ := hD Dstar hDs
  refine ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
    hbirth haq phi hphi hpinch u t hut hT₀u hlast hslabs hcurrent hfinal y R A β Λ Dcap θcap hR hA
    hβ hΛR hu hθ4 hθ hθΘ hDc hqΛ hbud htop hwin
  exact hD H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow hbirth
    haq phi hphi hpinch u t hut hT₀u hlast hslabs hcurrent hfinal y R A β Λ Dcap θcap hR hA hβ hΛR
    hu hθ4 hθ hθΘ hDc
    (H.pickedBall_scalar_le_along_traces_C11PB hslabs hcurrent hfinal hR (by linarith) hqΛ hu hbud
      htop) hwin

end SurvivalOrCap

section SliceContract

/-- **hpick（`_C11PB`，PROVISIONAL binder）**：二次选点球 `B_v(w, Rad/√q)`（`q := R(v, w)`，`K.event j`
incoming flow）上 `R(v, x) ≤ Λ q`。owner = selection / point-picking 车道（slice 内二次选点，
`Λ = 4`；P6SEL / ALPHA 的二次尺度选点）。K-SW / ShortSLT 输入面**不**需要它；它是 ODE 共同窗口与
`PickedBallSurvivalOrCap_C11PB` 的输入。 -/
def PickedBallTop_C11PB (Λ Rad : ℝ) (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) (v : ℝ)
    (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    (K.toHistory.event j).incoming.flow.scalar v x ≤
      Λ * (K.toHistory.event j).incoming.flow.scalar v w

/-- **witness 半（`_C11PB`）**：球 `B_v(w, Rad/√q)` 上 `R > qthr` 处 spatial canonical witness（neck
chart）= ShortSLT 的 `hW`、K-SW `hU` 第一项。**PROVED** ⇐ hgood + 中心 seed 余量 + `Rad ≤ L/2`
（`pickedBallWitness_of_hgood_C11PB`，只在切片时刻 `v`）。 -/
def PickedBallWitness_C11PB (Rad qthr ε C1 C2 : ℝ) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    qthr < (K.toHistory.event j).incoming.flow.scalar v x →
    ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
      ε C1 C2 x, W.capTubeHasNeckChart ε

/-- **hgrad（`_C11PB`，PROVISIONAL binder）**：共同窗口 `v′ ∈ (time j⁻, v)`、`v − β/q ≤ v′` 上，球
`B_v(w, Rad/√q)` 的点在 `R(v′, x) > qthr` 处的梯度界 `|∇R| ≤ Cgrad R^{3/2}` = ShortSLT 的 `hgrad`、
K-SW `hU` 第二项。owner = SHALLOW-TOOLS M1 / DIST（`[v − β/q, v]` 上球点 seed-distance 的 first-exit
closure，输入 = `SurvivalOrCap` 的 Rm 界）+ canonical neighbourhood 的梯度估计（hgood 的
`HasSpatialCanonicalTimeControl` 只含 witness 与时间导数，不含梯度）。 -/
def PickedBallGrad_C11PB (β Rad qthr : ℝ) (Cgrad : ℝ≥0) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time j.castSucc) v,
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
    qthr < (K.toHistory.event j).incoming.flow.scalar v' x →
    ∀ ξ : TangentSpace ThreeModel x,
      |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
        Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
          Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
          Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)

/-- **hUside（`_C11PB`）**：`PickedBallWitness_C11PB ∧ PickedBallGrad_C11PB`（ShortSLT 的 `hW` / `hgrad`、
K-SW `hU` 前两项，窗口 `β`）。 -/
def PickedBallWitnessGrad_C11PB (β Rad qthr ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) (v : ℝ)
    (w : (K.stage j.castSucc).Carrier) : Prop :=
  PickedBallWitness_C11PB Rad qthr ε C1 C2 K j v w ∧ PickedBallGrad_C11PB β Rad qthr Cgrad K j v w

/-- **hκ（`_C11PB`，PROVISIONAL binder）**：共同窗口 `τ ∈ [v − β/q, v] ∩ (time j⁻, time j⁺)` 上，球
`B_v(w, Rad/√q)` 的点处半径 `≤ ρ` 的 parabolically controlled ball κ-noncollapsed（同一背景 `κ`）。
= ShortSLT 的 `hnc`、K-SW 的 `hU` 第三项。owner = KAPPA / HFOOT（D-9(3)：κ footprint 覆盖实际
controlled balls）。 -/
def PickedBallKappa_C11PB (β Rad ρ κ : ℝ) (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (v : ℝ) (w : (K.stage j.castSucc).Carrier) : Prop :=
  ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
    v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
    K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
    ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
    ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
    ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
          (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
          (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)

/-- **picked-ball 短窗合同（`_C11PB`，PROVISIONAL）**：`PickedBallTop ∧ PickedBallWitnessGrad ∧
PickedBallKappa`（球 `B_v(w, Rad/√q)`、共同窗口 `[v − β/q, v]`、阈值 `qthr`、κ 半径 `ρ`）。 -/
def PickedBallShortWindow_C11PB (β Λ Rad qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) (v : ℝ)
    (w : (K.stage j.castSucc).Carrier) : Prop :=
  PickedBallTop_C11PB Λ Rad K j v w ∧ PickedBallWitnessGrad_C11PB β Rad qthr ε C1 C2 Cgrad K j v w ∧
    PickedBallKappa_C11PB β Rad ρ κ K j v w

variable {K : RetainedCoreHistory.{u}} {j : Fin K.eventCount} {v : ℝ}
  {w : (K.stage j.castSucc).Carrier}

/-- **hpick 单调（`_C11PB`）**：`Λ ≤ Λ′`、`Rad′ ≤ Rad`。 -/
theorem PickedBallTop_C11PB.mono {Λ Λ' Rad Rad' : ℝ}
    (hR : 0 ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hΛ : Λ ≤ Λ') (hRad : Rad' ≤ Rad)
    (h : PickedBallTop_C11PB Λ Rad K j v w) : PickedBallTop_C11PB Λ' Rad' K j v w := by
  have hsub := riemannianBallOf_mono ((K.toHistory.event j).incoming.flow.base.metric v) w
    (div_le_div_of_nonneg_right hRad
      (Real.sqrt_nonneg ((K.toHistory.event j).incoming.flow.scalar v w)))
  exact fun x hx => (h x (hsub hx)).trans (mul_le_mul_of_nonneg_right hΛ hR)

/-- **hUside 单调（`_C11PB`）**：窗口 `β′ ≤ β`、半径 `Rad′ ≤ Rad`、阈值 `qthr ≤ qthr′`（`q > 0`）。 -/
theorem PickedBallWitnessGrad_C11PB.mono {β β' Rad Rad' qthr qthr' ε C1 C2 : ℝ} {Cgrad : ℝ≥0}
    (hR : 0 < (K.toHistory.event j).incoming.flow.scalar v w) (hβ : β' ≤ β) (hRad : Rad' ≤ Rad)
    (hq : qthr ≤ qthr') (h : PickedBallWitnessGrad_C11PB β Rad qthr ε C1 C2 Cgrad K j v w) :
    PickedBallWitnessGrad_C11PB β' Rad' qthr' ε C1 C2 Cgrad K j v w := by
  have hsub := riemannianBallOf_mono ((K.toHistory.event j).incoming.flow.base.metric v) w
    (div_le_div_of_nonneg_right hRad
      (Real.sqrt_nonneg ((K.toHistory.event j).incoming.flow.scalar v w)))
  have hwin : v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤
      v - β' / (K.toHistory.event j).incoming.flow.scalar v w := by
    linarith [div_le_div_of_nonneg_right hβ hR.le]
  exact ⟨fun x hx hqx => h.1 x (hsub hx) (hq.trans_lt hqx),
    fun x hx v' hv' hvv' hqx ξ => h.2 x (hsub hx) v' hv' (hwin.trans hvv') (hq.trans_lt hqx) ξ⟩

/-- **hκ 单调（`_C11PB`）**：窗口 `β′ ≤ β`、半径 `Rad′ ≤ Rad`、κ 半径 `ρ′ ≤ ρ`（`q > 0`）。 -/
theorem PickedBallKappa_C11PB.mono {β β' Rad Rad' ρ ρ' κ : ℝ}
    (hR : 0 < (K.toHistory.event j).incoming.flow.scalar v w) (hβ : β' ≤ β) (hRad : Rad' ≤ Rad)
    (hρ : ρ' ≤ ρ) (h : PickedBallKappa_C11PB β Rad ρ κ K j v w) :
    PickedBallKappa_C11PB β' Rad' ρ' κ K j v w := by
  have hsub := riemannianBallOf_mono ((K.toHistory.event j).incoming.flow.base.metric v) w
    (div_le_div_of_nonneg_right hRad
      (Real.sqrt_nonneg ((K.toHistory.event j).incoming.flow.scalar v w)))
  have hwin : v - β / (K.toHistory.event j).incoming.flow.scalar v w ≤
      v - β' / (K.toHistory.event j).incoming.flow.scalar v w := by
    linarith [div_le_div_of_nonneg_right hβ hR.le]
  intro τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hball
  exact h τ (hwin.trans hτ1) hτ2 hτ3 hτ4 z (hsub hz) zz hzz b hb (hbρ.trans hρ) hball

/-- **合同单调（`_C11PB`）**：各分量单调的合取。 -/
theorem PickedBallShortWindow_C11PB.mono {β β' Λ Λ' Rad Rad' qthr qthr' ρ ρ' κ ε C1 C2 : ℝ}
    {Cgrad : ℝ≥0} (hR : 0 < (K.toHistory.event j).incoming.flow.scalar v w) (hβ : β' ≤ β)
    (hΛ : Λ ≤ Λ') (hRad : Rad' ≤ Rad) (hq : qthr ≤ qthr') (hρ : ρ' ≤ ρ)
    (h : PickedBallShortWindow_C11PB β Λ Rad qthr ρ κ ε C1 C2 Cgrad K j v w) :
    PickedBallShortWindow_C11PB β' Λ' Rad' qthr' ρ' κ ε C1 C2 Cgrad K j v w :=
  ⟨h.1.mono hR.le hΛ hRad, h.2.1.mono hR hβ hRad hq, h.2.2.mono hR hβ hRad hρ⟩

/-- **inhabitant（`_C11PB`）**：`Rad = 0` 时球为空，合同平凡成立（定义一致性检查；实际内容在
`Rad ≥` ShortSLT 的 `Rad` 处）。 -/
theorem pickedBallShortWindow_zero_C11PB (β Λ qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0) :
    PickedBallShortWindow_C11PB β Λ 0 qthr ρ κ ε C1 C2 Cgrad K j v w := by
  have hempty : ∀ x, x ∉ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
      (0 / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)) := by
    intro x hx
    simp [riemannianBallOf] at hx
  exact ⟨fun x hx => absurd hx (hempty x),
    And.intro (fun x hx => absurd hx (hempty x)) (fun x hx => absurd hx (hempty x)),
    fun _ _ _ _ _ z hz => absurd hz (hempty z)⟩

end SliceContract

section SurvivalOrCapSlice

open DifferentialGeometry.Geometry.Metric

/-- **整球存活或实际 cap（slice 层，`_C11PB`）**：`B_v(w, A/√R)`（`K.event j` incoming metric）的每点有
backward trace 起于某 `first ≤ j⁻`、`time first ≤ v − β/R`（TP `htrace` 结论形），或 `w` 是 late
`CapWindowPoint`（K-SW / LS3 的 CWP 形：实际 records、`‖x‖ < Dcap + 1`、`v − time i⁺ ≤ θcap / scale`）。 -/
def PickedBallSurvivalOrCapSlice_C11PB (K : RetainedCoreHistory.{u}) {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (j : Fin K.eventCount) (v : ℝ) (w : (K.stage j.castSucc).Carrier) (R A β Dcap θcap : ℝ) :
    Prop :=
  (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w (A / Real.sqrt R),
    ∃ (first : Fin (K.eventCount + 1)) (hf : first ≤ j.castSucc), K.time first ≤ v - β / R ∧
      Nonempty (BackwardPointTrace K.toHistory first j.castSucc hf x)) ∨
  ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
    (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
    (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
    B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
      v - K.time i.succ ≤ θcap * (((records i hT).static b).neck.scale)⁻¹

/-- **slice 时刻的 active stage（`_C11PB`）**：`time j⁻ < v < time j⁺` ⇒ `activeStage ⟨v, _⟩ = j⁻`
（`BackwardTraceDistortion` 私有引理的公开副本）。 -/
theorem RetainedCoreHistory.activeStage_eq_castSucc_C11PB (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (t : Icc (0 : ℝ) K.toHistory.horizon) (h1 : K.time j.castSucc < t)
    (h2 : (t : ℝ) < K.time j.succ) : K.toHistory.activeStage t = j.castSucc := by
  apply le_antisymm _ (K.toHistory.le_activeStage t j.castSucc h1.le)
  by_contra h
  have hlt : j.castSucc < K.toHistory.activeStage t := lt_of_not_ge h
  have hs : j.succ ≤ K.toHistory.activeStage t := Fin.castSucc_lt_iff_succ_le.mp hlt
  have hle := (K.toHistory.time_strictMono.monotone hs).trans (K.toHistory.activeStage_time_le t)
  exact absurd h2 (not_lt.mpr hle)

/-- **generic-stage 形（`_C11PB`，内部）**：对 `k = activeStage t` 的任意改名，ObservedHistory 层的
`pickedBall_survivalOrCap_C11PB` 结论的存活支化为 `∃ first ≤ k, time first ≤ t − β/R ∧ trace`。 -/
theorem RetainedCoreHistory.survival_of_isTracedRegion_C11PB (K : RetainedCoreHistory.{u})
    (t : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stage (K.toHistory.activeStage t)).Carrier) {ρ τ Krm : ℝ}
    (h : K.toHistory.isTracedRegion t y ρ τ Krm) :
    ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y ρ,
      ∃ (first : Fin (K.eventCount + 1)) (hf : first ≤ K.toHistory.activeStage t),
        K.time first ≤ (t : ℝ) - τ ∧
        Nonempty (BackwardPointTrace K.toHistory first (K.toHistory.activeStage t) hf x) := by
  obtain ⟨-, -, a, hat, ha, hall⟩ := h
  intro x hx
  obtain ⟨A, -⟩ := hall x hx
  exact ⟨K.toHistory.activeStage a, K.toHistory.activeStage_mono hat,
    (K.toHistory.activeStage_time_le a).trans (le_of_eq ha), ⟨A⟩⟩

/-- **picked-ball 整球存活或实际 cap（slice 层，`_C11PB`，PROVED）**：`pickedBall_survivalOrCap_C11PB` 在
slice `time j⁻ < v < time j⁺` 处的实例（`t := ⟨v, _⟩`、`u := ⟨v − β/q, _⟩`、`q := R(v, w)`；
`activeStage t = j⁻`，`hlast` / `hfinal` 空真，`hcurrent` = event `j` 的 `DerivativeBoundBefore`）。
球顶输入 = 合同字段 `PickedBallTop_C11PB Λ A`（hpick）。 -/
theorem RetainedCoreHistory.pickedBall_survivalOrCap_slice_C11PB :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ Dstar : ℝ, StandardCap.transitionEnd < Dstar →
    ∃ Rrad : ℝ, Dstar + 1 < Rrad ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale) →
      (∀ i hi b, 1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici T₀) phi) →
    ∀ (j : Fin H.eventCount) (v : ℝ), H.time j.castSucc < v → v < H.time j.succ →
      H.EventSlabsDerivative C qcan j.castSucc →
      (H.toHistory.event j).incoming.DerivativeBoundBefore C qcan v →
    ∀ (w : (H.stage j.castSucc).Carrier) (A β Λ Dcap θcap : ℝ),
      0 ≤ v - β / (H.toHistory.event j).incoming.flow.scalar v w →
      T₀ ≤ v - β / (H.toHistory.event j).incoming.flow.scalar v w →
      0 < (H.toHistory.event j).incoming.flow.scalar v w → 0 < A → 0 < β →
      1 ≤ Λ * (H.toHistory.event j).incoming.flow.scalar v w →
      1 / 4 ≤ θcap → 1 - c / (8 * β * Λ) ≤ θcap → θcap < Θ → Dcap ≤ Dstar →
      qcan ≤ Λ * (H.toHistory.event j).incoming.flow.scalar v w → (C : ℝ) * Λ * β ≤ 1 / 2 →
      PickedBallTop_C11PB Λ A H j v w →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * Λ) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Λ * β) * A < Dcap →
      PickedBallSurvivalOrCapSlice_C11PB H records j v w
        ((H.toHistory.event j).incoming.flow.scalar v w) A β Dcap θcap := by
  obtain ⟨c, hc, hD⟩ := RetainedCoreHistory.pickedBall_survivalOrCap_C11PB.{u}
  refine ⟨c, hc, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨Cbirth, hCb, hD⟩ := hD Θ hΘ hΘ1 C
  refine ⟨Cbirth, hCb, fun Dstar hDs => ?_⟩
  obtain ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, hD⟩ := hD Dstar hDs
  refine ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
    hbirth haq phi hphi hpinch j v hv1 hv2 hslabK hderK w A β Λ Dcap θcap hu0 hT₀u hR hA hβ hΛR
    hθ4 hθ hθΘ hDc hqΛ hbud htop hwin
  have hβR : 0 ≤ β / (H.toHistory.event j).incoming.flow.scalar v w := div_nonneg hβ.le hR.le
  have hvh : v ≤ H.toHistory.horizon := hv2.le.trans (H.toHistory.time_le_horizon_at _)
  let t : Icc (0 : ℝ) H.toHistory.horizon := ⟨v, by linarith, hvh⟩
  let u : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨v - β / (H.toHistory.event j).incoming.flow.scalar v w, hu0, by linarith⟩
  have hut : u ≤ t := by
    change v - β / (H.toHistory.event j).incoming.flow.scalar v w ≤ v
    linarith
  have hact : H.toHistory.activeStage t = j.castSucc :=
    H.activeStage_eq_castSucc_C11PB j t hv1 hv2
  have hne : j.castSucc ≠ Fin.last H.eventCount := (Fin.castSucc_lt_last j).ne
  have key : ∀ (k : Fin (H.eventCount + 1)) (hk : H.toHistory.activeStage t = k)
      (y : (H.toHistory.stage k).Carrier),
      H.EventSlabsDerivative C qcan k →
      (∀ i : Fin H.eventCount, i.castSucc = k →
        (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t) →
      k ≠ Fin.last H.eventCount →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) y
          (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar v w)),
        metricScalarAt (H.toHistory.stageMetric k t) x ≤
          Λ * (H.toHistory.event j).incoming.flow.scalar v w) →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) y
          (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar v w)),
        ∃ (first : Fin (H.eventCount + 1)) (hf : first ≤ k),
          H.time first ≤ v - β / (H.toHistory.event j).incoming.flow.scalar v w ∧
          Nonempty (BackwardPointTrace H.toHistory first k hf x)) ∨
      ∃ (i : Fin H.eventCount) (hT : T₀ ≤ H.time i.succ) (hl : i.succ ≤ k)
        (B : BackwardPointTrace H.toHistory i.succ k hl y)
        (b : (H.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - H.time i.succ ≤ θcap * (((records i hT).static b).neck.scale)⁻¹ := by
    intro k hk y hs hc hkl htop'
    subst hk
    have hres := hD H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
      hbirth haq phi hphi hpinch u t hut hT₀u (fun hl => absurd hl hkl) hs hc
      (fun _ hl => absurd hl hkl) y ((H.toHistory.event j).incoming.flow.scalar v w) A β Λ Dcap
      θcap hR hA hβ hΛR rfl hθ4 hθ hθΘ hDc hqΛ hbud htop' hwin
    rcases hres with htr | hcap
    · exact Or.inl (H.survival_of_isTracedRegion_C11PB t y htr)
    · exact Or.inr hcap
  have hc : ∀ i : Fin H.eventCount, i.castSucc = j.castSucc →
      (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t := by
    intro i hi
    obtain rfl := Fin.castSucc_injective _ hi
    exact hderK
  have htop' : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric j.castSucc t) w
      (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar v w)),
      metricScalarAt (H.toHistory.stageMetric j.castSucc t) x ≤
        Λ * (H.toHistory.event j).incoming.flow.scalar v w := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact htop
  have hres := key j.castSucc hact w hslabK hc hne htop'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  exact hres

end SurvivalOrCapSlice

section WitnessFromHgood

/-- **hUside 的 witness 半（`_C11PB`，PROVED：空间余量）**：selection 的 `HgoodCg_C11SH Cg`（Kh 层，
`Kh n = (K n).toHistory`）+ 中心 `w` 的 seed 余量 `d_v(O, w) ≤ dσ + (L/2)/√R_n`（K-SW 消费面 `hUVC`
的 Good(L/2) 条件，K 层形）+ `R_n ≤ R(v, w)` + `0 ≤ Rad ≤ L/2` ⇒ 球 `B_v(w, Rad/√R(v, w))` 上
`R > Cg·R_n` 处 spatial canonical witness（= `PickedBallWitnessGrad_C11PB` 的第一项，阈值 `Cg·R_n`）。
空间余量：`d_v(O, x) ≤ d_v(O, w) + Rad/√R(v, w) ≤ dσ + L/√R_n`；时间域 `[σ − L²/R_n, σ]`、`aSeed ≤ v`
照 hgood。只在切片时刻 `v`（不需时间窗）；梯度半仍是 binder。 -/
theorem pickedBallWitness_of_hgood_C11PB {Cg : ℝ} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctime : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) (j : Fin (K n).eventCount) (v : Icc (0 : ℝ) (K n).toHistory.horizon)
    (hv1 : (K n).time j.castSucc < v) (hv2 : (v : ℝ) < (K n).time j.succ)
    (hav : aSeed n ≤ v) (hvs : v ≤ σ n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ} (hRn : 0 < R n)
    (hRw : R n ≤ ((K n).toHistory.event j).incoming.flow.scalar v w) (hRad0 : 0 ≤ Rad)
    (hRadL : Rad ≤ L n / 2)
    (hw : riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
        ((seedTrace n).point j.castSucc h1 h2) w ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) :
    PickedBallWitness_C11PB Rad (Cg * R n) eps C1 C2 (K n) j v w := by
  intro x hx hRx
  have hsRn : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRn
  have hsle : Real.sqrt (R n) ≤
      Real.sqrt (((K n).toHistory.event j).incoming.flow.scalar v w) := Real.sqrt_le_sqrt hRw
  have hL0 : 0 ≤ L n / 2 / Real.sqrt (R n) := div_nonneg (hRad0.trans hRadL) hsRn.le
  have hrad : Rad / Real.sqrt (((K n).toHistory.event j).incoming.flow.scalar v w) ≤
      L n / 2 / Real.sqrt (R n) :=
    (div_le_div_of_nonneg_left hRad0 hsRn hsle).trans
      (div_le_div_of_nonneg_right hRadL hsRn.le)
  have hhalf : ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) +
      ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) = ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [← ENNReal.ofReal_add hL0 hL0]
    congr 1
    ring
  have hxd : riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
        ((seedTrace n).point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    calc riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
          ((seedTrace n).point j.castSucc h1 h2) x
        ≤ riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
            ((seedTrace n).point j.castSucc h1 h2) w +
          riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n)) ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) :=
          add_le_add hw (hx.le.trans (ENNReal.ofReal_le_ofReal hrad))
      _ = _ := by rw [add_assoc, hhalf]
  have hact := (K n).activeStage_eq_castSucc_C11PB j v hv1 hv2
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage v = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k v) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k v) x' →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k v) eps C1 C2 x',
        W.capTubeHasNeckChart eps := by
    intro k hk h1' h2' x' hd hR'
    subst hk
    exact (hgood n v hav hvs hvL x' hd hR').1
  have hxd' : riemannianEDistOf ((K n).toHistory.stageMetric j.castSucc v)
        ((seedTrace n).point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hxd
  have hRx' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric j.castSucc v) x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hRx.le
  have hres := key j.castSucc hact h1 h2 x hxd' hRx'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  exact hres

/-- **hUside 构造（`_C11PB`）**：hgood 付 witness 半（`pickedBallWitness_of_hgood_C11PB`）+ binder hgrad
⇒ `PickedBallWitnessGrad_C11PB β Rad (Cg·R_n)`。故 hUside 的真正缺项只剩 `PickedBallGrad_C11PB`。 -/
theorem pickedBallWitnessGrad_of_hgood_C11PB {Cg β : ℝ} {Cgrad : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctime : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) (j : Fin (K n).eventCount) (v : Icc (0 : ℝ) (K n).toHistory.horizon)
    (hv1 : (K n).time j.castSucc < v) (hv2 : (v : ℝ) < (K n).time j.succ)
    (hav : aSeed n ≤ v) (hvs : v ≤ σ n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j.castSucc)
    (h2 : j.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (w : ((K n).stage j.castSucc).Carrier) {Rad : ℝ} (hRn : 0 < R n)
    (hRw : R n ≤ ((K n).toHistory.event j).incoming.flow.scalar v w) (hRad0 : 0 ≤ Rad)
    (hRadL : Rad ≤ L n / 2)
    (hw : riemannianEDistOf (((K n).toHistory.event j).incoming.flow.base.metric v)
        ((seedTrace n).point j.castSucc h1 h2) w ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / 2 / Real.sqrt (R n)))
    (hgrad : PickedBallGrad_C11PB β Rad (Cg * R n) Cgrad (K n) j v w) :
    PickedBallWitnessGrad_C11PB β Rad (Cg * R n) eps C1 C2 Cgrad (K n) j v w :=
  ⟨pickedBallWitness_of_hgood_C11PB K hgood n j v hv1 hv2 hav hvs hvL h1 h2 w hRn hRw hRad0 hRadL
    hw, hgrad⟩

end WitnessFromHgood

section Consumers

/-- **consumer：ShortSLT 输入面 ⇐ 合同（`_C11PB`，PROVISIONAL：binder `ShortSLT_C11KS θ`）**：
`slice_scalar_bound_of_not_capWindowPoint_short_C11KS` 的常数前缀；`U := B_v(w, Rad/√q)`，
`hW / hgrad / hnc`
由 `PickedBallWitnessGrad / PickedBallKappa`（窗口 `β ≥ θ`、半径 `Rad′ ≥ Rad`、阈值 `q`）缩窗供给；`hnot`
改为分情形：结论 = 中心 late CWP（年龄 `θ`）**或** `B_v(w, A/√q)` 上 `R ≤ Q q`。导数界照旧是全局输入。 -/
theorem RetainedCoreHistory.capWindowPoint_or_scalar_bound_of_pickedBall_C11PB
    {θ β : ℝ} (hS : ShortSLT_C11KS.{u} θ) (hθβ : θ ≤ β)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (v : ℝ), K.time j.castSucc < v → v < K.time j.succ →
    ∀ (w : (K.stage j.castSucc).Carrier) (q ρ : ℝ),
      T₀ ≤ v - θ / (K.toHistory.event j).incoming.flow.scalar v w →
      0 < q → q ≤ Cq * (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w) →
    ∀ Rad' : ℝ, Rad ≤ Rad' →
      PickedBallWitnessGrad_C11PB β Rad' q ε C1 C2 Cgrad K j v w →
      PickedBallKappa_C11PB β Rad' ρ κ K j v w →
      ∀ qd : ℝ, qd ≤ q → K.EventSlabsDerivative Ctime qd j.castSucc →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qd v →
      (∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ θ * (((records i hT).static b).neck.scale)⁻¹) ∨
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_short_C11KS hS hεle κ C1 C2 hκ
      Ctime Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, ?_⟩
  intro K j p T₀ records hcan hRr hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ Rad'
    hRad hWG hKap qd hqd hslab hderG
  refine (Classical.em _).imp id fun hcw => ?_
  have hRpos : 0 < (K.toHistory.event j).incoming.flow.scalar v w :=
    lt_of_lt_of_le (zero_lt_one.trans_le hΛ) hΛR
  have hWG' := hWG.mono hRpos hθβ hRad le_rfl
  exact hmain K j T₀ records hcan hRr hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ
    _ (fun x hx => hx) hWG'.1 qd hqd hslab hderG hWG'.2 (hKap.mono hRpos hθβ hRad le_rfl) hcw

/-- **K-SW 逐点 `hU` ⇐ 合同（`_C11PB`）**：`slice_dichotomy_late_Cg_window_P6LS3` / `KSW_C11KS θ₀` 的
U 侧三元（阈值 `Cg · R_n`、窗口 `θ₀`、半径 `Rad`）⇐ `PickedBallWitnessGrad β Rad′ (Cg · R_n)` ∧
`PickedBallKappa β Rad′`（`θ₀ ≤ β`、`Rad ≤ Rad′`、`R_n ≤ R(v, w)`、`0 < R_n`）。 -/
theorem kswHU_of_pickedBall_C11PB {θ₀ β Rad Rad' Cg Rn ρ κ ε C1 C2 : ℝ} {Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {j : Fin K.eventCount} {v : ℝ}
    {w : (K.stage j.castSucc).Carrier} (hRn : 0 < Rn)
    (hRw : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w) (hθβ : θ₀ ≤ β)
    (hRad : Rad ≤ Rad')
    (hWG : PickedBallWitnessGrad_C11PB β Rad' (Cg * Rn) ε C1 C2 Cgrad K j v w)
    (hKap : PickedBallKappa_C11PB β Rad' ρ κ K j v w) :
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
      Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
        ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
      ∀ v' ∈ Ioo (K.time j.castSucc) v,
      v - θ₀ / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
      Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
          Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
            Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
            Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ₀ / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
            (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) := by
  have hR := hRn.trans_le hRw
  obtain ⟨h1, h2⟩ := hWG.mono hR hθβ hRad le_rfl
  exact ⟨h1, h2, hKap.mono hR hθβ hRad le_rfl⟩

/-- **consumer：K-SW 二分 ⇐ 合同（`_C11PB`，PROVISIONAL：binder `KSW_C11KS θ₀`）**：`KSW_C11KS θ₀` 的陈述
逐字，只把逐点 U 侧前提 `hU` 换成 picked-ball 合同族：对每个合格 `w`（离 `z` `< Dd/√R_n`、seed 余量
`d1 + Dd/√R_n`、`R_n ≤ R(v, w)`）给 `PickedBallWitnessGrad β Rad′ (Cg · R_n) ∧ PickedBallKappa β Rad′`
（`θ₀ ≤ β`、任意 `Rad′ ≥ Rad`）。证明 = `kswHU_of_pickedBall_C11PB` 逐点喂 `hK`。 -/
theorem ksw_of_pickedBall_C11PB {θ₀ β : ℝ} (hθβ : θ₀ ≤ β) (hK : KSW_C11KS.{u} θ₀) :
  ∀ {ε : ℝ}, ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0) (Cg : ℝ),
    0 < Cg → ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi → ∀ {η₃ Lc : ℝ},
    0 < η₃ → 0 < Lc →
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < ζmin ∧ 0 < δ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rmin ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζmin →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord K.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        pF.delta (K.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i hT b, qcan ≤ Cbirth * ((records i hT).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hT).static b).neck.scale) →
    ∀ (j : Fin K.eventCount), K.EventSlabsDerivative Ctime qcan j.castSucc →
    ∀ v : ℝ, K.time j.castSucc < v → v < K.time j.succ →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan v →
    ∀ (Rn ρ : ℝ), 0 < Rn → qcan ≤ Cg * Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
      T₀ ≤ v - θ₀ / Rn →
    ∀ (k : Fin (K.eventCount + 1)), k = j.castSucc →
    ∀ (z sk : (K.toHistory.stage k).Carrier) (sj : (K.stage j.castSucc).Carrier), HEq sk sj →
    ∀ d1 : ENNReal, riemannianEDistOf (K.toHistory.stageMetric k v) sk z ≤ d1 →
    ∀ zj : (K.stage j.castSucc).Carrier, HEq z zj →
    ∀ Rad' : ℝ, Rad ≤ Rad' →
    (∀ w : (K.stage j.castSucc).Carrier,
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sj w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) zj w <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w →
        PickedBallWitnessGrad_C11PB β Rad' (Cg * Rn) ε C1 C2 Cgrad K j v w ∧
          PickedBallKappa_C11PB β Rad' ρ κ K j v w) →
    ∃ CWP : (K.toHistory.stage k).Carrier → Prop,
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → ¬ CWP w →
        Rn ≤ metricScalarAt (K.toHistory.stageMetric k v) w → ∀ x,
        riemannianEDistOf (K.toHistory.stageMetric k v) w x <
          ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
            Real.sqrt (metricScalarAt (K.toHistory.stageMetric k v) w)) →
        metricScalarAt (K.toHistory.stageMetric k v) x ≤
          QB * metricScalarAt (K.toHistory.stageMetric k v) w) ∧
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → CWP w →
        ∃ (Ξ : standardCapWindow D₂ → (K.toHistory.stage k).Carrier)
          (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
          Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
          ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
            τw ∈ Icc (0 : ℝ) (1 / 2) ∧
            ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
              metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                  (K.toHistory.stageMetric k v)) Ξ hΞ)
                ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad Cg hCg phi hphi η₃ Lc hη₃ hLc
  obtain ⟨Cbirth, hCb, hmain⟩ := hK hεle κ C1 C2 hκ Ctime Cgrad Cg hCg hphi hη₃ hLc
  refine ⟨Cbirth, hCb, fun A Dd hA hDd => ?_⟩
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Rmin, ζmin, δ₀, m₀, hΛ, hζ, hδ, h⟩ := hmain A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Rmin, ζmin, δ₀, m₀, hΛ, hζ, hδ, ?_⟩
  intro K p T₀ records hcan hRr hord hacc hpinch pF recordsF δb hdelta hδb qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj Rad'
    hRad hPB
  exact h K T₀ records hcan hRr hord hacc hpinch recordsF δb hdelta hδb qcan a₀ hq0 hHI hlow hbirth
    j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj
    (fun w h1 h2 h3 => kswHU_of_pickedBall_C11PB hRn h3 hθβ hRad (hPB w h1 h2 h3).1
      (hPB w h1 h2 h3).2)

end Consumers

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
