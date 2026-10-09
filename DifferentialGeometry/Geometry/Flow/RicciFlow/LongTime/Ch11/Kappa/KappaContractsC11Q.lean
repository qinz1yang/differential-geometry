import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841ConsumerC11K
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.RegularEndpointBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimumPortC11P
import DifferentialGeometry.Geometry.Operator.Laplacian.Barrier

/-!
# 局部 κ 生产链 K0–K6：合同冻结 + 装配（O-CH11-KAPPA G1，后缀 `_C11Q`）

外审 R-C11-2 Q1.1 / 处置 D-R-C11-2-1 的七核 K0–K6，逐条写成**树内对象**上的 data-level
`def … : Prop`（不含 P6 / S8 / `AnalyticSurgeryProfile`），并装配成
`localKappa_of_K0_to_K6_C11Q : K0 → … → K6 → LocalKappaSupply_P6B F δ α nr`。

## 树内对象（合同只用这些，不另造抽象数据）
* **Ṽ**：`RetainedCoreHistory.reducedVolume k x T v`（`Surgery/Noncollapsing/ReducedVolumeBounds:43`，
  时钟 `v = √τ`）；**单调性**已证 `historyReducedVolumeMonotone_holds`。
* **admissible 曲线 / 作用量 𝓛**：`regularizedActionValues` / `regularizedCost`（经每个 event 的 `old`
  过渡，保留识别 `oldOutput`）；**barely admissible** = 经 `∂old` 过渡；**非 barely admissible 极小**
  = `regularMinimizerEndpoints`（`RegularCrossing`：`old` 的内点）。
* **cutoff 函数**：astra（FIX4 port）`physicalWeightedCost = φ(d/r − A(1 − 2v²/r²)) · (L̄ + 2 r v)`，
  `L̄ = 2v𝓛`，`φ = SingularBarrier.value`——即 `r² L̂`，`L̂ = L̄/r² + 2√τ/r`：KL v5 p.168
  (85.4)–(85.9) 的权重（**不是**无手术证明的 `L̄ + 7`）。

## 七核（种子尺度 `r`；时钟 `v = √τ`；数值比例冻结如下）
* **K0** `SeedPatchTransport_C11Q`：深度 `3r²/4` 切片上 `B(O⋆, r/20)` ⊆ `B_t(p, 3r/5)` 的 traced 像
  （**包含**）、体积 `≥ (w e⁻⁵⁷/512)ϱ³`、余量 `B(O⋆, 3r/40)` 回溯受控。
* **K1** `AdmissibleLCalculus_C11Q`：(a) 跨 regular seam 拼接（`𝓛` 三角不等式）；(b) 非 barely
  admissible 极小端点处 Perelman 变分不等式（上支撑 jets）。
* **K2** `LocalizedLCutoffInequality_C11Q`：半时钟 `v ≤ r/√2` 上 cutoff 最小值的右上支撑微分不等式
  （只在极小点为 regular 时）；只用种子（种子端局部 Ricci 上界），**不**假设 `B(p, Ar)` 上 Ricci 下界。
* **K3** `SurgeryActionBarrier_C11Q`：accuracy `δ < αA` 下，`𝓛 ≤ (Λ_A − 1) r` ⇒ regular 极小端点
  （barely admissible 排除）；cutoff 最小值低于屏障时可达（空间边界逃逸）。
* **K4** `BoundedReducedLengthNearSeed_C11Q`：深度 `r²/2` 的 `B(O, r/10)` 内有 `l ≤ C₄(A)` 的 regular
  极小端点。
* **K5** `SeedPatchLowAction_C11Q`（拼接段）+ 体积解释 ⇒ `SeedReducedVolumeLower_C11Q`：
  `Ṽ(3r²/4) ≥ v_A > 0`。
* **K6** `ControlledBallVolumeFromReducedVolume_C11Q`：`∀ η, ∃ σ_η C_η`，
  `Ṽ(σ_η ϱ²) ≤ C_η Vol B(x,ϱ)/ϱ³ + η` 且 `σ_η ϱ² ≤ θ r²`（`σ_η` 不固定为 1，含尾部 `η`）。

## 本文件证明的部分（非前提）
* `localKappaWide_of_reducedVolume_C11Q`：K5 + K6 + 树内单调性，`η = v_A/2` ⇒ `κ_A = v_A/(2C_η)`；
* 链 `localKappa_of_K0_to_K6_C11Q`（纯逻辑装配）与 consumer（经 P6B 的 L5 得 window 形）。
* 后续组（同目录新文件）：G2 证 K0；G3 由树内 `historyReducedVolumeLocalUpperBound_holds` 证 K6；
  G4 证 K4 ⇐ K2 + K3（极大值原理）与 K5 ⇐ K0 + K4 + K5a + 体积解释，并给 `Pre841` consumer。

## 基点测试球前提（rev2）
K2–K5 都带 **基点 `x` 的受控测试球** `P(x, t, ϱ₀, −ϱ₀²)`，`ϱ₀ ≥ nr(t)/100`（`nr` = neck radius）：
若 `x` 落在新鲜手术帽上（无此控制），从 `x` 出发的曲线必须先离开帽，作用量 `~h²/ε` 无界，`Ṽ`
无一致下界——K5 对无控制的 `x` 为假；树内屏障 `exists_uniform_regularMinimizerEndpoint_of_…`
也要 pole 受控球且 `δ₀` 依赖其半径。故链只给**同一 `nr`** 的供给（尺度 `≥ nr/100`），`nr = 0`
（小尺度）仍归 Q3（D-R-C11-2-4）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 0. 共用对象（全部是树内对象的薄包装） -/

/-- 历史 `R` 上的标量下界 `R ≥ −Bf`（regularized 作用量的截断参数取任一真实下界；
存在性 = 树内 `RetainedCoreHistory.exists_stageMetric_scalar_lower_bound`）。 -/
def ScalarFloor_C11Q (R : RetainedCoreHistory.{u}) (Bf : ℝ) : Prop :=
  ∀ j : Fin (R.eventCount + 1), ∀ s ∈ R.toHistory.stageDomain j,
    ∀ y : (R.stage j).Carrier, -Bf ≤ metricScalarAt (R.toHistory.stageMetric j s) y

/-- 基点时刻 `t`、时钟 `v = √τ` 的切片时刻 `t − v²`（`projIcc`，与树内 `reducedVolume` 同式）。 -/
def clockSlice_C11Q (R : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) R.toHistory.horizon)
    (v : ℝ) : Icc (0 : ℝ) R.toHistory.horizon :=
  projIcc 0 R.horizon R.horizon_nonneg ((t : ℝ) - v ^ 2)

/-- **Ṽ**：基点 `(t, x)` 的 reduced volume，后向深度 `τ`（树内 `RetainedCoreHistory.reducedVolume`
以时钟 `v = √τ` 为参数）。 -/
def redVolTau_C11Q (R : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) R.toHistory.horizon)
    (x : (R.toHistory.stageAt t).Carrier) (τ : ℝ) : ℝ≥0∞ :=
  R.reducedVolume (R.toHistory.activeStage t) x t (Real.sqrt τ)

/-- **𝓛**：基点 `(t, x)` 到切片 `s`（时钟 `√(t − s)`）上点 `q` 的 regularized 作用量下确界
（admissible 曲线 = 经每个 event 的 `old` 过渡；树内 `regularizedCost`）；阶段序不成立时 `⊤`。 -/
def sliceCost_C11Q (R : RetainedCoreHistory.{u}) (Bf : ℝ)
    (t s : Icc (0 : ℝ) R.toHistory.horizon) (x : (R.toHistory.stageAt t).Carrier)
    (q : (R.toHistory.stageAt s).Carrier) : WithTop ℝ :=
  if hle : R.toHistory.activeStage s ≤ R.toHistory.activeStage t then
    R.toHistory.regularizedCost (R.toHistory.activeStage s) (R.toHistory.activeStage t) hle t Bf
      0 (Real.sqrt ((t : ℝ) - s)) x q
  else ⊤

/-- **非 barely admissible 极小端点**：`q` 由一条经每个 event 的 `old` **内点**过渡
（`RegularCrossing`）的极小曲线达到（树内 `regularMinimizerEndpoints`）。 -/
def IsRegularMinimizerEndpoint_C11Q (R : RetainedCoreHistory.{u}) (Bf : ℝ)
    (t s : Icc (0 : ℝ) R.toHistory.horizon) (x : (R.toHistory.stageAt t).Carrier)
    (q : (R.toHistory.stageAt s).Carrier) : Prop :=
  ∃ hle : R.toHistory.activeStage s ≤ R.toHistory.activeStage t,
    q ∈ R.toHistory.regularMinimizerEndpoints (R.toHistory.activeStage s)
      (R.toHistory.activeStage t) hle t Bf (Real.sqrt ((t : ℝ) - s)) x

/-- **低作用量端点**（K4 / K5 的通货）：非 barely admissible 极小端点，且 reduced length
`l = 𝓛/(2√τ) ≤ C`。与树内 `exists_test_volume_lower_of_regular_endpoint_block` 的 block 前提同形。 -/
def IsLowActionEndpoint_C11Q (R : RetainedCoreHistory.{u}) (Bf : ℝ)
    (t s : Icc (0 : ℝ) R.toHistory.horizon) (x : (R.toHistory.stageAt t).Carrier) (C : ℝ)
    (q : (R.toHistory.stageAt s).Carrier) : Prop :=
  IsRegularMinimizerEndpoint_C11Q R Bf t s x q ∧
    sliceCost_C11Q R Bf t s x q ≤ ((2 * C * Real.sqrt ((t : ℝ) - s) : ℝ) : WithTop ℝ)

/-- 时钟 `v` 处 cutoff 函数在点 `q` 的值：astra `physicalWeightedCost`
`= φ(d_{t−v²}(O, q)/r − A(1 − 2v²/r²)) · (L̄ + 2 r v)`（截断区外 `⊤`）；中心 `O` = 种子 trace 在切片
`t − v²` 的点（切片落在 `[b, t]` 外时记 `⊤`）。 -/
def cutoffValue_C11Q (R : RetainedCoreHistory.{u}) (Bf r A : ℝ)
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) (v : ℝ)
    (q : (R.toHistory.stageAt (clockSlice_C11Q R t v)).Carrier) : WithTop ℝ :=
  if h : b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t then
    R.toHistory.physicalWeightedCost (R.toHistory.activeStage (clockSlice_C11Q R t v))
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono h.2) t Bf r A v x
      (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t v))
        (R.toHistory.activeStage_mono h.1) (R.toHistory.activeStage_mono h.2)) q
  else ⊤

/-- **cutoff 最小值** `M(v) = inf_q h(q, v)`（`h` = `cutoffValue_C11Q`）。 -/
def cutoffMin_C11Q (R : RetainedCoreHistory.{u}) (Bf r A : ℝ)
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) (v : ℝ) : WithTop ℝ :=
  sInf (Set.range (cutoffValue_C11Q R Bf r A hbt seedTrace x v))

/-- **归一化 cutoff 最小值** `N(v) = M(v)/(2rv) · e^{−(Cv²/r² + 32v/r)}`（`M = ⊤` 时记 `0`；K2 另断言
`M < ⊤`）。KL：`h₀(τ) ≲ 2√τ · exp(C(A)τ + c√τ)`（种子归一化）；与 astra 的单调量
（`IncomingEventWeightedMinimumPortC11P` 的 `exp(−Cv²/r²−32v/r)·m(v)/v`）同形。 -/
def cutoffMinNormalized_C11Q (R : RetainedCoreHistory.{u}) (Bf r A C : ℝ)
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) (v : ℝ) : ℝ :=
  WithTop.untopD (0 : ℝ) (cutoffMin_C11Q R Bf r A hbt seedTrace x v) / (2 * r * v) *
    Real.exp (-(C * v ^ 2 / r ^ 2 + 32 * v / r))

/-! ## K0 `seed_patch_transport` -/

/-- **K0 产物**（深度 `3r²/4` 的早期切片 `s`）：种子 `(p, t, r)`、种子 trace `b = t − r² → t`，
中心 `O = seedTrace` 在 `s` 的点。
1. **包含 + 度量比较**：`B_s(O, r/20)` 的每点 `y` 都是某个 `x' ∈ B_t(p, 3r/5)` 的 Rm-controlled
  （半径 `√3 r`）backward trace 在 `s` 的点——终端球的 traced 像 ⊇ 早期固定比例度量球（不是把 traced
  像当成同半径度量球；半径比 `12 > e^{9/4}` 吸收 Ricci 畸变 `g_t ≤ e^{9/2} g_s`）；
2. **体积下界**：`vol B_s(O, ϱ) ≥ (w e⁻⁵⁷/512) ϱ³`（`0 < ϱ ≤ r/2`）；
3. **内部余量**：`B_s(O, 3r/40)` 每点都有从 `b` 起、Rm-controlled（半径 `r`）的 backward trace
  （retained identifications = trace 的 `RegularCrossing`）。 -/
def IsSeedPatch_C11Q (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r w : ℝ) (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t)
    (seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p)
    (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hst : s ≤ t) : Prop :=
  (∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
      (seedTrace.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))
      (r / 20),
    ∃ x' ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (3 * r / 5),
    ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x',
      A.isRmControlled (hat := hbt) (Real.sqrt 3 * r) ∧
      A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst) = y) ∧
  (∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ r / 2 →
    ENNReal.ofReal ((w * Real.exp (-57) / 512) * ϱ ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage s) s)
        (seedTrace.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))
        ϱ) ∧
  (∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
      (seedTrace.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))
      (3 * r / 40),
    ∃ B : BackwardPointTrace H (H.activeStage b) (H.activeStage s) (H.activeStage_mono hbs) y,
      B.isRmControlled (hat := hbs) r)

/-- **K0 `seed_patch_transport`**（合同；G2 证）：每个种子 `(p, t, r)`（`2r² < t`、
`hasSmallParabolicCurvature`、`vol B(p, r) ≥ w r³`）与种子 trace，在深度 `3r²/4` 的切片上给出
`IsSeedPatch_C11Q`。 -/
def SeedPatchTransport_C11Q : Prop :=
  ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r w : ℝ),
    2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hst : s ≤ t),
      (s : ℝ) = (t : ℝ) - 3 * r ^ 2 / 4 →
      IsSeedPatch_C11Q H t p r w b hbt seedTrace s hbs hst

/-! ## K1 `admissible_L_calculus` -/

/-- **K1 `admissible_L_calculus`**（合同；同一 surgery history `R` 上）。定义部分全是树内对象
（admissible = `regularizedActionValues`，barely admissible = 经 `∂old` 过渡，非 barely 极小 =
`regularMinimizerEndpoints`，作用量 = `regularizedExtendedAction`；加权 Jacobian ⇒ Ṽ 单调已是树内
`historyReducedVolumeMonotone_holds`，不列为字段）。需证的两条：
* (a) **跨 regular seam 的兼容（拼接）**：`𝓛_t(x → q@s₂) ≤ 𝓛_t(x → y@s₁) + 𝓛_t(y@s₁ → q@s₂)`；
* (b) **变分不等式**（Perelman I §7 的上支撑形，时钟 `v`，`n = 3`）：在 stage 开时段内的非 barely
  admissible 极小端点 `q`，`𝓛` 有 `C²` 上支撑 `F`，`∇F = V`（终点速度）、
  `∂_v F = 2v²R − ½|V|²`、`ΔF < 3/v − vR − 𝓛/(2v²) + |V|²/(4v) + ε`——即 astra
  `weighted_physical_history_support_heat_lower_at_minimum` 的输入形。 -/
def AdmissibleLCalculus_C11Q (R : RetainedCoreHistory.{u}) : Prop :=
  (∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (t s₁ s₂ : Icc (0 : ℝ) R.toHistory.horizon) (h₂₁ : s₂ ≤ s₁) (h₁t : s₁ ≤ t)
      (x : (R.toHistory.stageAt t).Carrier) (y : (R.toHistory.stageAt s₁).Carrier)
      (q : (R.toHistory.stageAt s₂).Carrier),
      R.toHistory.regularizedCost (R.toHistory.activeStage s₂) (R.toHistory.activeStage t)
          (R.toHistory.activeStage_mono (h₂₁.trans h₁t)) t Bf 0 (Real.sqrt ((t : ℝ) - s₂)) x q ≤
        R.toHistory.regularizedCost (R.toHistory.activeStage s₁) (R.toHistory.activeStage t)
            (R.toHistory.activeStage_mono h₁t) t Bf 0 (Real.sqrt ((t : ℝ) - s₁)) x y +
          R.toHistory.regularizedCost (R.toHistory.activeStage s₂) (R.toHistory.activeStage s₁)
            (R.toHistory.activeStage_mono h₂₁) t Bf (Real.sqrt ((t : ℝ) - s₁))
            (Real.sqrt ((t : ℝ) - s₂)) y q) ∧
  (∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (t : Icc (0 : ℝ) R.toHistory.horizon) (x : (R.toHistory.stageAt t).Carrier)
      (first : Fin (R.eventCount + 1)) (hle : first ≤ R.toHistory.activeStage t) (v : ℝ),
      0 < v → (t : ℝ) - v ^ 2 ∈ Ioo (R.toHistory.time first) (R.toHistory.stageEndTime first) →
      ∀ q ∈ R.toHistory.regularMinimizerEndpoints first (R.toHistory.activeStage t) hle t Bf v x,
      let g := R.toHistory.stageMetric first ((t : ℝ) - v ^ 2)
      ∃ L : ℝ, R.toHistory.regularizedCost first (R.toHistory.activeStage t) hle t Bf 0 v x q =
          (L : WithTop ℝ) ∧
      ∃ V : TangentSpace ThreeModel q, ∀ ε : ℝ, 0 < ε →
      ∃ (U : Set ((R.stage first).Carrier × ℝ)) (F : (R.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧ ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
        F (q, v) = L ∧
        (∀ z ∈ U, R.toHistory.regularizedCost first (R.toHistory.activeStage t) hle t Bf 0 z.2 x
          z.1 ≤ (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * metricScalarAt g q - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * metricScalarAt g q - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + ε)

/-! ## K2 `localized_L_cutoff_inequality` -/

/-- **K2 `localized_L_cutoff_inequality`**（合同）：对 `A > 0` 给常数 `C₂ A`；对每个种子
`(p, t, r)`（**只用种子**：其抛物控制给种子端 `B(O_s, θr)` 的局部 Ricci 上界；**不**假设放大球
`B(p, Ar)` 上的 Ricci 下界）、种子 trace（cutoff 中心 `O_s`）、基点 `x ∈ B_t(p, Ar)`（带受控测试球
`ϱ₀ ≥ nr(t)/100`）与标量下界 `Bf`，在半时钟
`0 < v ≤ r/√2` 上：
* cutoff 最小值 `M(v) < ⊤`，归一化 `N(v) = M(v)/(2rv)·e^{−(C₂v²/r² + 32v/r)}` 连续；
* 初值：`∀ ε > 0, ∃ v₀`，`N(v₀) ≤ 1 + ε`（`v → 0` 时 `M ≈ 2rv`）；
* **微分不等式**（尚未碰到 surgery 边界处）：若 `M(v)` 在某个**非 barely admissible** 极小端点
  达到，则 `N` 在 `v` 处有右上支撑，导数 `≤ ε`（`∀ ε > 0`）。 -/
def LocalizedLCutoffInequality_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (nr : ℝ → ℝ) (C₂ : ℝ → ℝ) : Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
      (∀ v ∈ Ioc 0 (r / Real.sqrt 2), cutoffMin_C11Q R Bf r A hbt seedTrace x v < ⊤) ∧
      ContinuousOn (cutoffMinNormalized_C11Q R Bf r A (C₂ A) hbt seedTrace x)
        (Ioc 0 (r / Real.sqrt 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ v₀ ∈ Ioo 0 (r / Real.sqrt 2),
        cutoffMinNormalized_C11Q R Bf r A (C₂ A) hbt seedTrace x v₀ ≤ 1 + ε) ∧
      ∀ v ∈ Ioo 0 (r / Real.sqrt 2),
        (∃ q, cutoffValue_C11Q R Bf r A hbt seedTrace x v q =
            cutoffMin_C11Q R Bf r A hbt seedTrace x v ∧
          IsRegularMinimizerEndpoint_C11Q R Bf t (clockSlice_C11Q R t v) x q) →
        ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ, ∃ d : ℝ,
          ψ v = cutoffMinNormalized_C11Q R Bf r A (C₂ A) hbt seedTrace x v ∧
          cutoffMinNormalized_C11Q R Bf r A (C₂ A) hbt seedTrace x ≤ᶠ[𝓝[>] v] ψ ∧
          HasDerivWithinAt ψ d (Ioi v) v ∧ d ≤ ε

/-! ## K3 `surgery_action_barrier` -/

/-- **K3 `surgery_action_barrier`**（合同）：对 `A > 0` 给屏障 `Λ A`；在 accuracy `δ < αA`
（`[t/2, t]` 上，即参数小性；生产者用真实 surgery records、标准帽演化与标量下界）下，对每个种子、
种子 trace、基点（带受控测试球 `ϱ₀ ≥ nr(t)/100`）与半时钟 `0 < v ≤ r/√2`：
* **barely admissible 排除**：`𝓛(q) ≤ (Λ_A − 1) r`（即 `L̂ ≤ Λ_A · 2v/r`）⇒ `q` 是非 barely
  admissible 极小端点（极小存在，且只经 `old` 内点过 event）；
* **空间边界逃逸**：`M(v) < Λ_A · 2rv` ⇒ cutoff 最小值被达到（极小化序列不逃逸）。 -/
def SurgeryActionBarrier_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (Λ : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ v ∈ Ioc 0 (r / Real.sqrt 2),
      (∀ q : (H.stageAt (clockSlice_C11Q R t v)).Carrier,
        sliceCost_C11Q R Bf t (clockSlice_C11Q R t v) x q ≤ (((Λ A - 1) * r : ℝ) : WithTop ℝ) →
        IsRegularMinimizerEndpoint_C11Q R Bf t (clockSlice_C11Q R t v) x q) ∧
      (cutoffMin_C11Q R Bf r A hbt seedTrace x v < ((Λ A * (2 * r * v) : ℝ) : WithTop ℝ) →
        ∃ q, cutoffValue_C11Q R Bf r A hbt seedTrace x v q =
          cutoffMin_C11Q R Bf r A hbt seedTrace x v)

/-! ## K4 `bounded_reduced_length_near_seed` -/

/-- **K4 `bounded_reduced_length_near_seed`**（合同；K2 + K3 + 极大值原理的产物）：在 accuracy 下、
基点带受控测试球 `ϱ₀ ≥ nr(t)/100` 时，
深度 `r²/2` 的切片 `s₁` 上，种子 trace 点 `O₁` 的 `B(O₁, r/10)` 内存在 `l ≤ C₄(A)` 的非 barely
admissible 极小端点。 -/
def BoundedReducedLengthNearSeed_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (C₄ : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (s₁ : Icc (0 : ℝ) H.horizon) (hbs₁ : b ≤ s₁) (hs₁t : s₁ ≤ t),
      (s₁ : ℝ) = (t : ℝ) - r ^ 2 / 2 →
      ∃ q ∈ riemannianBallOf (H.stageMetric (H.activeStage s₁) s₁)
          (seedTrace.point (H.activeStage s₁) (H.activeStage_mono hbs₁)
            (H.activeStage_mono hs₁t)) (r / 10),
        IsLowActionEndpoint_C11Q R Bf t s₁ x (C₄ A) q

/-! ## K5 `seed_reduced_volume_lower` -/

/-- **K5a（K5 的拼接段，合同）**：K0 的 patch（深度 `3r²/4`）+ K4 的低作用量点（深度 `r²/2`，
`l ≤ C₄ A`）⇒ patch `B(O⋆, r/20)` 上处处 `l ≤ C₅ A`（把 K4 的极小曲线与种子区域内的连接曲线
拼接：K1(a) + 受控区的作用量估计 + K3 给极小存在 / 非 barely admissible）；基点带受控测试球
`ϱ₀ ≥ nr(t)/100`。 -/
def SeedPatchLowAction_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (C₄ C₅ : ℝ → ℝ) : Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (s₁ : Icc (0 : ℝ) H.horizon) (hbs₁ : b ≤ s₁) (hs₁t : s₁ ≤ t),
      (s₁ : ℝ) = (t : ℝ) - r ^ 2 / 2 →
    ∀ (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hst : s ≤ t),
      (s : ℝ) = (t : ℝ) - 3 * r ^ 2 / 4 →
      IsSeedPatch_C11Q H t p r A⁻¹ b hbt seedTrace s hbs hst →
      (∃ q₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage s₁) s₁)
          (seedTrace.point (H.activeStage s₁) (H.activeStage_mono hbs₁)
            (H.activeStage_mono hs₁t)) (r / 10),
        IsLowActionEndpoint_C11Q R Bf t s₁ x (C₄ A) q₁) →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))
          (r / 20),
        IsLowActionEndpoint_C11Q R Bf t s x (C₅ A) q

/-- **K5 `seed_reduced_volume_lower`（Ṽ 形）**：对 `A > 0`，`v A > 0`，且在 accuracy 下每个种子、
基点 `x ∈ B_t(p, Ar)`（带受控测试球 `ϱ₀ ≥ nr(t)/100`）有 `Ṽ_{(t,x)}(3r²/4) ≥ v A`（固定种子归一化
深度 `τ⋆ = 3r²/4`）。 -/
def SeedReducedVolumeLower_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) (v : ℝ → ℝ) :
    Prop :=
  ∀ A, 0 < A → 0 < v A ∧ ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
      ENNReal.ofReal (v A) ≤ redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2)

/-! ## K6 `controlled_ball_volume_from_reduced_volume` -/

/-- **K6 `controlled_ball_volume_from_reduced_volume`**（合同；`θ` = K5 深度比例）：
`∀ η > 0, ∃ σ_η > 0, ∃ C_η > 0`，对每个 retained-core history、每个受控测试球
`P(x, t, ϱ, −ϱ²)`（`0 < ϱ ≤ r`）：`Ṽ(σ_η ϱ²) ≤ C_η Vol B(x, ϱ)/ϱ³ + η` 且 `σ_η ϱ² ≤ θ r²`。
`σ_η` 不固定为 1；`η` 即球外（尾部）积分的预算。 -/
def ControlledBallVolumeFromReducedVolume_C11Q (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ σ C : ℝ, 0 < σ ∧ 0 < C ∧
    ∀ (R : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) R.toHistory.horizon)
      (x : (R.toHistory.stageAt t).Carrier) (ϱ r : ℝ), 0 < ϱ → ϱ ≤ r →
      R.toHistory.isParabolicallyRmControlledBall t x ϱ →
      redVolTau_C11Q R t x (σ * ϱ ^ 2) ≤
          ENNReal.ofReal (C / ϱ ^ 3) *
            ballVolume (R.toHistory.stageMetric (R.toHistory.activeStage t) t) x ϱ +
          ENNReal.ofReal η ∧
        σ * ϱ ^ 2 ≤ θ * r ^ 2

/-! ## 装配：K5 + K6 + 树内单调性 ⇒ 局部 κ；K0 → … → K6 链 -/

/-- **尺度上沿参数化的 KL 84.1(a)**（lead (O1)，02:3x）：与 `LocalKappaAt_P6B` 同形，只把测试尺度上沿
`ρ' ≤ r` 换成 `ρ' ≤ L·r`（`L = 1` 即 P6B 形）。reduced-volume 论证对任意固定 `L` 成立
（`κ = κ(A, L)`：K6 取 `θ = 3/(4L²)` 使 `σ ϱ² ≤ 3r²/4 = τ⋆`），不需新数学前提；seed shift 后
（种子半径 `r/100`）window 上沿可取 `(A + 1) r`（`L = 100(A + 1)`）。 -/
def LocalKappaWideAt_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (A L κ : ℝ) : Prop :=
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) →
    (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ L * r → H.isParabolicallyRmControlledBall t x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ'

/-- 上沿参数化的供给：`∀ A > 0, ∀ L > 0, ∃ κ > 0`。 -/
def LocalKappaWideSupply_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) : Prop :=
  ∀ A L, 0 < A → 0 < L → ∃ κ, 0 < κ ∧ LocalKappaWideAt_C11Q F δ α nr A L κ

/-- `L = 1` 特化回 P6B 的 `hKappaLocal` 形。 -/
theorem LocalKappaWideSupply_C11Q.toP6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : LocalKappaWideSupply_C11Q F δ α nr) : LocalKappaSupply_P6B F δ α nr := by
  intro A hA
  obtain ⟨κ, hκ, hW⟩ := h A 1 hA one_pos
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  exact hW n t p r hr hacc hsmall hvol x hx ρ' hlow (by rwa [one_mul]) hball

/-- **K5 + K6 + 正确方向的单调性 ⇒ 局部 κ（上沿 `L r`）**（审稿 Q1.1 第三限定）：取 `η = v_A/2`，
K6（`θ = 3/(4L²)`）给 `σ, C` 且 `σ ϱ² ≤ 3r²/4 = τ⋆`，树内 `historyReducedVolumeMonotone_holds` 给
`v_A ≤ Ṽ(τ⋆) ≤ Ṽ(σ ϱ²) ≤ C Vol B(x, ϱ)/ϱ³ + v_A/2`，故 `κ = v_A/(2C)` 只依赖 `v_A, C`
（即 `A, L`）。K5 在测试球自身（`ϱ₀ = ρ' ≥ nr/100`）处调用。 -/
theorem localKappaWide_of_reducedVolume_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeLower_C11Q F δ α nr v)
    (hK6 : ∀ θ : ℝ, 0 < θ → ControlledBallVolumeFromReducedVolume_C11Q.{u} θ) :
    LocalKappaWideSupply_C11Q F δ α nr := by
  intro A L hA hL
  obtain ⟨hvA, h5⟩ := hK5 A hA
  obtain ⟨σ, C, hσ, hC, h6⟩ := hK6 (3 / (4 * L ^ 2)) (by positivity) (v A / 2) (half_pos hvA)
  refine ⟨v A / 2 / C, div_pos (half_pos hvA) hC, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  have hρ : 0 < ρ' := hball.1
  have hr0 : 0 < r := hsmall.1
  obtain ⟨hupper, hdepth⟩ := h6 (F.tower.history n) t x ρ' (L * r) hρ hup hball
  have hθ : 3 / (4 * L ^ 2) * (L * r) ^ 2 = 3 / 4 * r ^ 2 := by
    field_simp
  rw [hθ] at hdepth
  have hlowV := h5 n t p r hr hacc hsmall hvol x hx ρ' hlow hball
  have hτ : 0 < σ * ρ' ^ 2 := by positivity
  have hmono : redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2) ≤
      redVolTau_C11Q (F.tower.history n) t x (σ * ρ' ^ 2) := by
    unfold redVolTau_C11Q
    refine historyReducedVolumeMonotone_holds (F.tower.history n) _ x t _ _
      ((F.tower.history n).toHistory.activeStage_mem t) (Real.sqrt_pos.2 hτ)
      (Real.sqrt_le_sqrt hdepth) ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hchain := (hlowV.trans hmono).trans hupper
  set V := ballVolume (H.stageMetric (H.activeStage t) t) x ρ' with hV
  have hsplit : ENNReal.ofReal (v A) =
      ENNReal.ofReal (v A / 2) + ENNReal.ofReal (v A / 2) := by
    rw [← ENNReal.ofReal_add (half_pos hvA).le (half_pos hvA).le]
    congr 1
    ring
  rw [hsplit] at hchain
  have hhalf : ENNReal.ofReal (v A / 2) ≤ ENNReal.ofReal (C / ρ' ^ 3) * V :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have hρ3 : 0 < ρ' ^ 3 := pow_pos hρ 3
  have hreal : v A / 2 / C * ρ' ^ 3 = v A / 2 * (ρ' ^ 3 / C) := by
    field_simp
  have hone : C / ρ' ^ 3 * (ρ' ^ 3 / C) = 1 := by
    field_simp
  calc
    ENNReal.ofReal (v A / 2 / C * ρ' ^ 3) =
        ENNReal.ofReal (v A / 2) * ENNReal.ofReal (ρ' ^ 3 / C) := by
      rw [hreal, ENNReal.ofReal_mul (half_pos hvA).le]
    _ ≤ ENNReal.ofReal (C / ρ' ^ 3) * V * ENNReal.ofReal (ρ' ^ 3 / C) :=
      mul_le_mul_left hhalf _
    _ = V := by
      rw [mul_comm (ENNReal.ofReal (C / ρ' ^ 3)) V, mul_assoc,
        ← ENNReal.ofReal_mul (div_pos hC hρ3).le, hone, ENNReal.ofReal_one, mul_one]

/-- `L = 1`：K5 + K6 ⇒ P6B 的 `hKappaLocal`（同一 `nr`）。 -/
theorem localKappa_of_reducedVolume_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeLower_C11Q F δ α nr v)
    (hK6 : ∀ θ : ℝ, 0 < θ → ControlledBallVolumeFromReducedVolume_C11Q.{u} θ) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappaWide_of_reducedVolume_C11Q hK5 hK6).toP6B

/-- **链定理（纯逻辑装配）** `K0 → K1 → K2 → K3 → K4 → K5 → K6 → LocalKappaWideSupply_C11Q`
（`.toP6B` 得 `LocalKappaSupply_P6B`）：各核作显式前提，依赖箭头照审稿表——K2 由 K1 产出，K4 由
K2 + K3（极大值原理）产出，K5 由 K0 + K1 + K4（拼接 + 体积解释）产出；末段 K5 + K6 + 树内单调性见
`localKappaWide_of_reducedVolume_C11Q`。全部在同一 `nr`（基点测试球 `≥ nr/100`）。
（G3 用树内定理消去 `hK6`；G4 用 K2 + K3 证 `hK4`、用 K0 + K4 + K5a + 体积解释证 `hK5`。） -/
theorem localKappa_of_K0_to_K6_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₄ v : ℝ → ℝ}
    (hK0 : SeedPatchTransport_C11Q.{u})
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hK4 : LocalizedLCutoffInequality_C11Q F nr C₂ → SurgeryActionBarrier_C11Q F δ α nr Λ →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hK5 : SeedPatchTransport_C11Q.{u} → (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄ → SeedReducedVolumeLower_C11Q F δ α nr v)
    (hK6 : ∀ θ : ℝ, 0 < θ → ControlledBallVolumeFromReducedVolume_C11Q.{u} θ) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_reducedVolume_C11Q (hK5 hK0 hK1 (hK4 (hK2 hK1) hK3)) hK6

/-- **consumer（G1）**：K0–K6（同一 `nr`）+ S7 ⇒ `hKappaLocal` ⇒ P6B L5 的 window 形
`LocalKappaWindowAt_P6B F nr A κ`（`localKappaWindow_of_late_P6B`）——P6 point selection 的消费形；
`nr = 0` window / `Pre841` 还要 Q3 的小尺度补充（G4 consumer 经 SMALLVOL 的 window glue）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₄ v : ℝ → ℝ}
    (hK0 : SeedPatchTransport_C11Q.{u})
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hK4 : LocalizedLCutoffInequality_C11Q F nr C₂ → SurgeryActionBarrier_C11Q F δ α nr Λ →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hK5 : SeedPatchTransport_C11Q.{u} → (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄ → SeedReducedVolumeLower_C11Q F δ α nr v)
    (hK6 : ∀ θ : ℝ, 0 < θ → ControlledBallVolumeFromReducedVolume_C11Q.{u} θ)
    (hacc : LargerBallAccuracySupply_C11S δ α) :
    ∀ A, 0 < A → ∃ κ, 0 < κ ∧ LocalKappaWindowAt_P6B F nr A κ :=
  localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc
    (localKappa_of_K0_to_K6_C11Q hK0 hK1 hK2 hK3 hK4 hK5 hK6).toP6B)

end GC.LongTime.Ch11
