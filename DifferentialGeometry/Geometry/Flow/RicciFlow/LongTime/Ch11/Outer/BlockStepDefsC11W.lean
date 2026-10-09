import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData

set_option autoImplicit false

/-!
# O-CH11-OUTER (G2)：outer 本体 block-step 合同 (W-step) 的 data-level 骨架

外审 R-C11-2 D-13 / D-14 / D-15（design：`docs/geometrization/chapter8/
design-C11-outer-block-step-20261007.md`）。块 `b_j = preparedSpatialHorizon j`（0, 1, 3, 9, …），
capacity `3^j = b_{j+1}`；时间骨架冻结：activation `(5/6)·3^j`、`η_j = 1/(j+2)`。

* `BlockState_C11W j` = astra `PreparedSpatialState pBase C P g (b_j) (3^j)`：到 `b_j` 的实际有限
  history、同事件 records、冻结 schedule（`parameters` 在 `[0, b_j]` 上的值）、prefix / metric
  identifications（`initial`、`affine`、`finalMetric_heq`）、native tail 与 prepared class
  （lookahead 到 `3^j`）、已构造前缀上的 `noncollapsed` / `canonical`。
* `Inv_C11W`：已构造前缀上的证书与估计（fit、reserve quality、`DistanceData`、`C.Ctime` 导数界）。
* (W-schedule) 第 `j` 项 = `BlockLookahead_C11W X`（`nextClass` 以 restart datum 为类型索引、
  `rNext`；由 step 第一阶段选，先于 fine request）+ `BlockRequest_C11W`（fine request、cap）。
* `ReadyForNextBlock_C11W X ℓ req` = `LookaheadReady_C11W`（重启识别 + overlap 控制；overlap
  两项结构性免费 `overlap_of_state_C11W`）∧ `RequestReady_C11W`（实际预算 + 相邻块前瞻）；
  **不含**"存在延拓"。
* `PhysicalExtension_C11W X Y ℓ req d`：`PreparedSpatialSuccessor` + restart 等式 + schedule
  实现 + `PreparedSpatialStepRetention`（CertificatesExtend）。
* `BudgetChoice_C11W j`（W0，**已证** `budgetChoice_C11W`）、`BlockStep_C11W j`（W1–W4，astra
  `exists_prepared_spatial_step` 的量词顺序：∃ lookahead，∀ 合格 request，∃ 延拓）：brief 授权的
  显式合同。
* `BlockTower_C11W`（W5 对象）、`toChain`、`tower_of_blockSteps_C11W`：纯逻辑装配，无占位证明。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- (W-step) 的 State_j：astra `PreparedSpatialState` 在 `(b_j, 3^j)` 处（字段清单见模块 doc）。 -/
abbrev BlockState_C11W (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (j : ℕ) : Type _ :=
  PreparedSpatialState pBase C P g (preparedSpatialHorizon j) ((3 : ℝ) ^ j)

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- (W-schedule) 的 restart lookahead（由 step 的第一阶段选出，先于 fine request）：下一 native
class（建在 `X` 的 restart datum = 最后一个 native stage 上，capacity `3^(j+1) − b`）与下一半径。 -/
structure BlockLookahead_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j) where
  nextClass : ClosedBirthPreparedClass pBase C (X.native.stage (Fin.last X.native.eventCount))
    (X.native.initialMetric (Fin.last X.native.eventCount))
    ((3 : ℝ) ^ (j + 1) - X.history.time (Fin.last X.history.eventCount))
  rNext : ℝ

/-- (W-schedule) 的 fine request 与 accuracy cap（W0 在 lookahead 之后 online 选）。 -/
structure BlockRequest_C11W where
  epsCut : ℝ
  Dcut : ℝ
  mcut : ℕ
  accuracyCap : ℝ

/-- `BlockRequest_C11W` 的 inhabitant。 -/
def BlockRequest_C11W.unit : BlockRequest_C11W := ⟨1, 1, 0, 1⟩

/-- 已构造前缀上的时间导数控制（S11 / EP6）：常数是 Γ 里的 `C.Ctime`（与 `j` 无关，D-14
统一量），阈值是当前半径 `(radius²)⁻¹`；形状与 astra `derivative_bound_on_old_native_tail`
的结论逐字同。 -/
def TimeDerivativeControl_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j) : Prop :=
  ∀ (k : Fin (X.history.eventCount + 1)) (y : (X.history.stage k).Carrier) (s : ℝ),
    s ∈ Ioo (X.history.time k) (X.history.toHistory.stageEndTime k) →
    (X.radius ^ 2)⁻¹ < metricScalarAt (X.history.toHistory.stageMetric k s) y →
    |derivWithin (fun v => metricScalarAt (X.history.toHistory.stageMetric k v) y)
      (Iic s) s| ≤ C.Ctime * metricScalarAt (X.history.toHistory.stageMetric k s) y ^ 2

/-- Inv_j：只含已构造前缀上的证书与估计。 -/
structure Inv_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) {j : ℕ}
    (X : BlockState_C11W pBase C P g j) : Prop where
  fit : X.radius * Real.sqrt X.prepared.Qall ≤ 100 * cMax
  reserve : X.prepared.HasReserveQuality Dstar εReserve
  distance : X.DistanceData Cdist
  timeDerivative : TimeDerivativeControl_C11W X

/-- Ready 的 lookahead 半：重启识别（下一 class 在 restart datum 上、半径阈值、small-test
margin、class 质量）+ 已有 overlap 控制（当前 native tail 在 `[shift, b_j]` 上的估计）。 -/
structure LookaheadReady_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) {j : ℕ}
    (X : BlockState_C11W pBase C P g j) (ℓ : BlockLookahead_C11W X) : Prop where
  rNext_pos : 0 < ℓ.rNext
  rNext_le : ℓ.rNext ≤ X.radius
  threshold : ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹
  fit : ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax
  next_reserve : ℓ.nextClass.HasReserveQuality Dstar εReserve
  next_distance : ℓ.nextClass.HasDistanceExtension Cdist
  overlap_noncollapsed : X.native.NoncollapsedBefore X.prepared.kappa C.epsilon X.native.horizon
  overlap_estimates : NativeEstimates X.native C.epsilon C.C1 C.C2 C.C1s C.C2s
    X.prepared.qcan X.prepared.qs C.tauMin C.Ctime C.Cgrad

/-- Ready 的预算半：实际预算 + 相邻块前瞻（下一块精度 ≤ seam 处当前精度的四分之一）。 -/
structure RequestReady_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j)
    (req : BlockRequest_C11W) : Prop where
  cap_pos : 0 < req.accuracyCap
  cap_le_level : req.accuracyCap ≤ 1 / ((j : ℝ) + 2)
  cap_le_quarter : req.accuracyCap ≤ X.parameters.delta (preparedSpatialHorizon j) / 4
  epsCut_pos : 0 < req.epsCut
  Dcut_pos : 0 < req.Dcut

/-- ReadyForNextBlock_j = lookahead 半 ∧ 预算半（全部是关于 `X ℓ req` 的具体性质；没有
"存在延拓"）。 -/
structure ReadyForNextBlock_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) {j : ℕ}
    (X : BlockState_C11W pBase C P g j) (ℓ : BlockLookahead_C11W X)
    (req : BlockRequest_C11W) : Prop where
  lookahead : LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ
  request : RequestReady_C11W X req

/-- PhysicalExtension：`X ↪ Y`（`horizon Y = b_{j+1}` 在类型里）。`successor` 给 prefix / metric
identification、RecordsExtend（`records_preserved`）、ScheduleExtends（`parameters_past`）；
restart 与 schedule 的实现等式；`retention` 给 CertificatesExtend。 -/
structure PhysicalExtension_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j)
    (Y : BlockState_C11W pBase C P g (j + 1)) (ℓ : BlockLookahead_C11W X)
    (req : BlockRequest_C11W) (d : ℝ) : Prop where
  successor : PreparedSpatialSuccessor X Y ((5 / 6 : ℝ) * 3 ^ j) (1 / ((j : ℝ) + 2)) d
  accuracy_pos : 0 < d
  accuracy_lt_one : d < 1
  accuracy_le_cap : d ≤ req.accuracyCap
  shift_eq : Y.shift = X.history.time (Fin.last X.history.eventCount)
  offset_eq : Y.offset = X.history.eventCount
  nativeStage_eq : Y.nativeStage = X.native.stage (Fin.last X.native.eventCount)
  nativeMetric_heq : HEq Y.nativeMetric (X.native.initialMetric (Fin.last X.native.eventCount))
  radius_eq : Y.radius = ℓ.rNext
  prepared_heq : HEq Y.prepared ℓ.nextClass
  retention : Nonempty (PreparedSpatialStepRetention X Y d (1 / ((j : ℝ) + 2))
    req.epsCut req.Dcut req.mcut)

variable (pBase C P g)

/-- W0（fine request 与 cap）：对每个 lookahead，存在满足预算半的 request。
（`budgetChoice_C11W` 证明它；RequestCertificate 需要的具体 policy 由 P6 / PRE841 侧给。） -/
def BudgetChoice_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (j : ℕ) : Prop :=
  ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
    ∀ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ →
      ∃ req : BlockRequest_C11W, RequestReady_C11W X req

/-- (W-step)（W1–W4 的合成；astra `exists_prepared_spatial_step` 的量词顺序）：Inv ⇒ 先选
restart lookahead（class + 半径，先于 fine request），再对每个合格 request 造到达 `b_{j+1}` 的
物理延拓 ∧ Inv。 -/
def BlockStep_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (j : ℕ) : Prop :=
  ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
    ∃ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ ∧
      ∀ req : BlockRequest_C11W, RequestReady_C11W X req →
        ∃ (Y : BlockState_C11W pBase C P g (j + 1)) (d : ℝ),
          PhysicalExtension_C11W X Y ℓ req d ∧ Inv_C11W Cdist cMax Dstar εReserve Y

/-- W5 对象：coherent block tower + (W-schedule) Σ（逐块 lookahead 与 request）+ 逐块证书
（(W+) 的同一 `d`）。 -/
structure BlockTower_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) where
  block : ∀ n : ℕ, BlockState_C11W pBase C P g n
  lookahead : ∀ n : ℕ, BlockLookahead_C11W (block n)
  request : ℕ → BlockRequest_C11W
  accuracy : ℕ → ℝ
  inv : ∀ n : ℕ, Inv_C11W Cdist cMax Dstar εReserve (block n)
  ready : ∀ n : ℕ,
    ReadyForNextBlock_C11W Cdist cMax Dstar εReserve (block n) (lookahead n) (request n)
  extension : ∀ n : ℕ,
    PhysicalExtension_C11W (block n) (block (n + 1)) (lookahead n) (request n) (accuracy n)
  initial_history : (block 0).history = RetainedCoreHistory.atZero P g
  initial_radius_le : (block 0).radius ≤ 1

variable {pBase C P g}

/-- 同一 prepared class 沿依赖索引的 HEq 运输：`Qall` 与 reserve quality 不变。 -/
theorem preparedClass_heq_transport_C11W {P Q : OrientedThreeStage.{u}} {g : P.Metric}
    {g' : Q.Metric} {B B' : ℝ} {K : ClosedBirthPreparedClass pBase C P g B}
    {K' : ClosedBirthPreparedClass pBase C Q g' B'} (hP : P = Q) (hg : HEq g g') (hB : B = B')
    (hK : HEq K K') (Dstar εReserve : ℝ) :
    K.Qall = K'.Qall ∧
      (K.HasReserveQuality Dstar εReserve ↔ K'.HasReserveQuality Dstar εReserve) := by
  cases hP
  cases eq_of_heq hg
  cases hB
  cases eq_of_heq hK
  exact ⟨rfl, Iff.rfl⟩

/-- overlap 控制结构性免费：`prepared.control` 作用于 state 自带的 native tail。 -/
theorem overlap_of_state_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j) :
    X.native.NoncollapsedBefore X.prepared.kappa C.epsilon X.native.horizon ∧
      NativeEstimates X.native C.epsilon C.C1 C.C2 C.C1s C.C2s
        X.prepared.qcan X.prepared.qs C.tauMin C.Ctime C.Cgrad := by
  obtain ⟨hnc, hest, -⟩ := X.prepared.control X.native X.nativeInitial X.nativeParameters
    X.nativeRecords X.native_lt_capacity.le X.nativeClass
  exact ⟨hnc, hest⟩

/-- LookaheadReady 的条件 inhabitant：只需下一 class / 半径的六项，overlap 两项由
`overlap_of_state_C11W` 给出。 -/
theorem lookaheadReady_of_class_C11W {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} {j : ℕ}
    {X : BlockState_C11W pBase C P g j} (ℓ : BlockLookahead_C11W X)
    (hr : 0 < ℓ.rNext) (hrle : ℓ.rNext ≤ X.radius)
    (hQ : ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹)
    (hfit : ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax)
    (hres : ℓ.nextClass.HasReserveQuality Dstar εReserve)
    (hdist : ℓ.nextClass.HasDistanceExtension Cdist) :
    LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ :=
  ⟨hr, hrle, hQ, hfit, hres, hdist, (overlap_of_state_C11W X).1, (overlap_of_state_C11W X).2⟩

/-- 冻结时间骨架：`0 ≤ b_j ≤ (5/6)·3^j < 3^j`（activation 落在第 `j` 块的 lookahead 区间内）。 -/
theorem blockActivation_mem_C11W (j : ℕ) :
    0 ≤ preparedSpatialHorizon j ∧ preparedSpatialHorizon j ≤ (5 / 6 : ℝ) * 3 ^ j ∧
      (5 / 6 : ℝ) * 3 ^ j < (3 : ℝ) ^ j := by
  have hp : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
  refine ⟨?_, ?_, by linarith⟩
  · cases j with
    | zero => exact le_rfl
    | succ n => exact (pow_pos (by norm_num : (0 : ℝ) < 3) n).le
  · cases j with
    | zero => norm_num [preparedSpatialHorizon]
    | succ n =>
      change (3 : ℝ) ^ n ≤ (5 / 6 : ℝ) * 3 ^ (n + 1)
      have hq : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
      rw [pow_succ]
      nlinarith

/-- **W0 是定理**：cap `= min (1/(j+2)) (δ(b_j)/4)`、`εcut = Dcut = 1`、`mcut = 0`。 -/
theorem budgetChoice_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (j : ℕ) :
    BudgetChoice_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  intro X _ _ _
  have hδ : 0 < X.parameters.delta (preparedSpatialHorizon j) :=
    X.parameters.delta_pos _ (blockActivation_mem_C11W j).1
  refine ⟨⟨1, 1, 0, min (1 / ((j : ℝ) + 2)) (X.parameters.delta (preparedSpatialHorizon j) / 4)⟩,
    ⟨lt_min (by positivity) (by positivity), min_le_left _ _, min_le_right _ _, one_pos,
      one_pos⟩⟩

namespace BlockTower_C11W

variable {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}

/-- W5 抽取：block tower 逐字段投影成 astra `PreparedSpatialChain`。 -/
def toChain (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) :
    PreparedSpatialChain pBase C P g where
  state := T.block
  accuracy := T.accuracy
  accuracy_pos n := (T.extension n).accuracy_pos
  accuracy_lt_one n := (T.extension n).accuracy_lt_one
  accuracy_le n := (T.extension n).accuracy_le_cap.trans (T.ready n).request.cap_le_level
  successor n := (T.extension n).successor
  initial_history := T.initial_history
  initial_radius_le := T.initial_radius_le

theorem toChain_state (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (n : ℕ) :
    T.toChain.state n = T.block n := rfl

/-- (W-schedule) 读出：链的第 `n` 个精度 ≤ 该块 cap ≤ seam 处精度的四分之一。 -/
theorem toChain_accuracy_le_quarter
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (n : ℕ) :
    T.toChain.accuracy n ≤ (T.block n).parameters.delta (preparedSpatialHorizon n) / 4 :=
  (T.extension n).accuracy_le_cap.trans (T.ready n).request.cap_le_quarter

end BlockTower_C11W

/-- W5 装配：`∀ j` 的 W0 与 (W-step) + `Inv_0 X₀` + base 条件 ⇒ 以 `X₀` 起头的 block tower
（`Nat.rec` + `Classical.choose`，与 astra Recursion 的 `Certified n` 写法同构）。 -/
theorem tower_of_blockSteps_C11W {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (hW0 : ∀ j, BudgetChoice_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, T.block 0 = X₀ := by
  classical
  let Certified (n : ℕ) :=
    {X : BlockState_C11W pBase C P g n // Inv_C11W Cdist cMax Dstar εReserve X}
  let look (n : ℕ) (X : Certified n) : BlockLookahead_C11W X.1 :=
    Classical.choose (hstep n X.1 X.2)
  have look_spec (n : ℕ) (X : Certified n) :=
    Classical.choose_spec (hstep n X.1 X.2)
  let req (n : ℕ) (X : Certified n) : BlockRequest_C11W :=
    Classical.choose (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have req_spec (n : ℕ) (X : Certified n) : RequestReady_C11W X.1 (req n X) :=
    Classical.choose_spec (hW0 n X.1 X.2 (look n X) (look_spec n X).1)
  have ext (n : ℕ) (X : Certified n) := (look_spec n X).2 (req n X) (req_spec n X)
  let next (n : ℕ) (X : Certified n) : Certified (n + 1) :=
    ⟨Classical.choose (ext n X), (Classical.choose_spec (Classical.choose_spec (ext n X))).2⟩
  let acc (n : ℕ) (X : Certified n) : ℝ := Classical.choose (Classical.choose_spec (ext n X))
  have next_spec (n : ℕ) (X : Certified n) :
      PhysicalExtension_C11W X.1 (next n X).1 (look n X) (req n X) (acc n X) :=
    (Classical.choose_spec (Classical.choose_spec (ext n X))).1
  let chain : ∀ n : ℕ, Certified n := fun n => Nat.rec ⟨X₀, hX₀⟩ (fun n X => next n X) n
  exact ⟨{ block := fun n => (chain n).1
           lookahead := fun n => look n (chain n)
           request := fun n => req n (chain n)
           accuracy := fun n => acc n (chain n)
           inv := fun n => (chain n).2
           ready := fun n => ⟨(look_spec n (chain n)).1, req_spec n (chain n)⟩
           extension := fun n => next_spec n (chain n)
           initial_history := hhist
           initial_radius_le := hrad }, rfl⟩

/-- **outer 终点**：(W-step) + `Inv_0` ⇒ 以 `X₀` 起头的 block tower（W0 已是定理
`budgetChoice_C11W`），其 `toChain : PreparedSpatialChain` 从 `X₀` 起头。 -/
theorem exists_chain_of_blockSteps_C11W {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      T.block 0 = X₀ ∧ T.toChain.state 0 = X₀ := by
  obtain ⟨T, hT⟩ := tower_of_blockSteps_C11W
    (budgetChoice_C11W Cdist cMax Dstar εReserve) hstep X₀ hX₀ hhist hrad
  exact ⟨T, hT, hT⟩

/-- base 的条件 inhabitant（W0-base）：capacity 1 的 prepared class（带 distance rule）⇒
`BlockState_C11W 0`，history = `atZero`、radius ≤ 1、`DistanceData`、small-test margin。 -/
theorem exists_blockState_base_C11W (Cdist : ℝ≥0) (cMax : ℝ) (hcMax : 0 < cMax)
    (prepared : ClosedBirthPreparedClass pBase C P g 1) (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist) :
    ∃ X : BlockState_C11W pBase C P g 0, X.DistanceData Cdist ∧
      X.history = RetainedCoreHistory.atZero P g ∧ X.radius ≤ 1 ∧
      X.radius * Real.sqrt X.prepared.Qall ≤ 100 * cMax ∧ HEq X.prepared prepared := by
  obtain ⟨S, hdist, hhist, -, -, -, -, -, -, hprep, -, -, hrad, hfit, -, -⟩ :=
    exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin Cdist cMax hcMax
      pBase C P g prepared hbase hprepared
  exact ⟨S, hdist, hhist, hrad, hfit, hprep⟩

/-- 第 0 块的导数界空真：`b_0 = 0`，没有内部时间。 -/
theorem timeDerivativeControl_zero_C11W (X : BlockState_C11W pBase C P g 0) :
    TimeDerivativeControl_C11W X := by
  intro k y s hs
  exfalso
  have hs' : s ∈ Ioo (X.history.toHistory.time k) (X.history.toHistory.stageEndTime k) := hs
  have h0 : 0 ≤ X.history.toHistory.time k := X.history.toHistory.time_nonneg k
  have h1 : X.history.toHistory.stageEndTime k ≤ X.history.toHistory.horizon :=
    X.history.toHistory.stageEndTime_le_horizon k
  have h2 : X.history.toHistory.horizon = 0 := X.horizon_eq
  linarith [hs'.1, hs'.2]

/-- `Inv_C11W` 的条件 inhabitant（W0-base 全部）：capacity 1 的 prepared class（参数 = `pBase`、
带 distance rule 与 reserve quality）⇒ 满足 `Inv_0` 的 `X₀`，history = `atZero`、radius ≤ 1。 -/
theorem exists_inv_base_C11W (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (hcMax : 0 < cMax)
    (prepared : ClosedBirthPreparedClass pBase C P g 1) (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist)
    (hres : prepared.HasReserveQuality Dstar εReserve) :
    ∃ X : BlockState_C11W pBase C P g 0, Inv_C11W Cdist cMax Dstar εReserve X ∧
      X.history = RetainedCoreHistory.atZero P g ∧ X.radius ≤ 1 := by
  obtain ⟨S, hdist, hhist, -, hstage, hmetric, -, -, -, hprep, hshift, -, hrad, hfit, -, -⟩ :=
    exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin Cdist cMax hcMax
      pBase C P g prepared hbase hprepared
  obtain ⟨-, hR⟩ := preparedClass_heq_transport_C11W hstage hmetric
    (by rw [hshift, sub_zero]) hprep Dstar εReserve
  exact ⟨S, ⟨hfit, hR.mpr hres, hdist, timeDerivativeControl_zero_C11W S⟩, hhist, hrad⟩

end GC.LongTime.Ch11
