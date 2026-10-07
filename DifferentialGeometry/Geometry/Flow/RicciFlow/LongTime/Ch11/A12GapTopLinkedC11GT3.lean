import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopLinkedC11GT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsWireC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.HcofWireC11HC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.RequestCofinalC11W4

set_option autoImplicit false

/-!
# S-CH11-GAPTOP3 G2：顶层 `hlinkfine` 由 S10 wire + S14 + HCOF 供给（后缀 `_C11GT3`）

`a12EnhancedFull_of_gaps_v2_C11GT2` 的 binder `hlinkfine : ∀ S, LinkedAndFine_C11GT2 S`
（GAPTOP2 G5）
= S10 出口 `hlinkS10` + S14 出口 `hfine_S14`。S10 轮（`f179afcd25`）落树后，`PreparedSpatialChain` 的
`observation n` 带不变量 `linked`、`PreparedSpatialStepRetention` 带字段 `fineLinked`，
`External/LinkedWindowsWireC11SL` 的两条出口恰好是 `LinkedAndFine_C11GT2 S` 两字段的形：

* `hlinkfine_of_chain_C11GT3`：`∀ {pB Γ} (S : PreparedSpatialChain pB Γ P g),
  LinkedAndFine_C11GT2 S`，
  **无前提**——`hlinkS10` 取 `linkedWindowsSupply_of_chain_C11SL`（tuple 的 `hstatic` + 五项 `hbridge`
  原样进 producer），`hfine_S14` 取 `lateLinkedHlink_of_chain_C11SL`（`fineLinked` 字段）。
  所以 v2 的 `hlinkfine` binder 在 v3 里消失（G3）。
* S14 供给的**组装**（`lateLinkedRecordsSupply_of_astra_C12X` 里 `hlink` 由上一条给，**剩余前提逐字列出**）：
  * `hcof_of_tower_C11GT3`：`hcof` 的来源 (i)——W0 的 tower 请求共尾
    （`tower_fine_request_eventually_C11W4`，v2 证明体里内联的那一段）；
  * `linkedPackage_of_chain_C11GT3`：S10 + S14 一起：`LinkedWindowsSupply_C11E records ∧
    LateLinkedRecordsSupply_C11E F q`。剩余前提 = tuple 的 `hTower hstatic hbridge`（W1 的同名合取项）、
    retention 族 `W`、`hfixed hrc`、`hmi`（outer m-i 子句的 tube 部分）、`hblock`（outer block 子句的 raw
    部分）、`hcof`；
  * `linkedPackage_of_cofinal_request_C11GT3`：`hcof` 的来源 (ii)——HCOF 的 outer 共尾 request
    （`hcof_of_cofinal_request_C11HC`；`W` 的 `εcut Dcut mcut` 取
    `preparedSpatialPhysicalQualityRequest`）。
  `hshift / hoffset` 不进这几条（它们只在 `exists_surgery_with_retained_raw_caps` 里产 `hmi / hblock`）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2 主定理**：`hlinkfine` binder（`LinkedAndFine_C11GT2 S`，全体 chain）在 S10 落树后无条件成立。 -/
theorem hlinkfine_of_chain_C11GT3 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pB Γ P g) :
    LinkedAndFine_C11GT2 S :=
  ⟨fun F q records hTower hstatic hbridge =>
      linkedWindowsSupply_of_chain_C11SL S F q records hTower hstatic hbridge,
    fun W => lateLinkedHlink_of_chain_C11SL S W⟩

/-- `hcof` 的来源 (i)：W0 tower 的请求共尾（`RequestCofinal_C11W4`）+ 任意 retention 族 `W` ⇒
`lateLinkedRecordsSupply_of_astra_C12X` 的 `hcof` 逐字形（v2 证明体里内联的同一段）。 -/
theorem hcof_of_tower_C11GT3 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve)
    (hcofT : ∀ j, RequestCofinal_C11W4 j (T.request j))
    (W : ∀ m, PreparedSpatialStepRetention (T.toChain.state m) (T.toChain.state (m + 1))
      (T.toChain.accuracy m) (1 / ((m : ℝ) + 2)) (T.request m).epsCut (T.request m).Dcut
      (T.request m).mcut) :
    ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
  intro D ζ m hζ
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
    (tower_fine_request_eventually_C11W4 T hcofT hζ D m)
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk (W k)
  exact ⟨h2, h1, h3⟩

/-- **S10 + S14 的组装**（`hcof` 取显式前提）：chain `S` 的 narrow tuple `(F, q, records)` 与 retention
族 `W` ⇒ `LinkedWindowsSupply_C11E records ∧ LateLinkedRecordsSupply_C11E F q`。`hlink` 不再是前提
（`lateLinkedHlink_of_chain_C11SL`）；剩余前提逐字：`hTower hstatic hbridge`（tuple 的 W1 合取项）、
`hfixed hrc`、`hmi`、`hblock`（`lateLinkedRecordsSupply_of_astra_C12X` 同名）、`hcof`。 -/
theorem linkedPackage_of_chain_C11GT3 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pB Γ P g)
    {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hTower : F.tower = S.tower)
    (hstatic : q.fixed = pB.fixed ∧ q.modelRadius = pB.modelRadius ∧ q.modelOrder = pB.modelOrder ∧
      q.modelAccuracy = pB.modelAccuracy ∧ q.recenterConstant = pB.recenterConstant)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static)
    (hfixed : q.fixed = pB.fixed) (hrc : q.recenterConstant = pB.recenterConstant)
    (hmi : ∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) (n : ℕ),
      (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ≤ (n : ℝ) →
      ∃ j : Fin (F.tower.history n).eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        HEq (records n j).delta ((W m).fineRecords i).delta ∧
        HEq (records n j).order ((W m).fineRecords i).order ∧
        HEq (records n j).neck ((W m).fineRecords i).neck)
    (hblock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
      ∃ m : ℕ, ∃ i : Fin (S.state (m + 1)).native.eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ≤ (3 : ℝ) ^ m ∧
        MetricCutCapEvent.SamePresentation
          (translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent
          ((F.tower.history n).toHistory.event j) ∧
        ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
          ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
            (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
              (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
              (W m).fineParameters.modelAccuracy b'),
            HEq b b' ∧ raw.hasCanonicalWindow ∧
            raw.delta = (((W m).fineRecords i).static b).delta ∧
            raw.order = (((W m).fineRecords i).static b).order ∧
            HEq raw.neck (((W m).fineRecords i).static b).neck ∧
            raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric)
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder) :
    LinkedWindowsSupply_C11E records ∧ LateLinkedRecordsSupply_C11E F q :=
  ⟨linkedWindowsSupply_of_chain_C11SL S F q records hTower hstatic hbridge,
    lateLinkedRecordsSupply_of_astra_C12X S W F q records hfixed hrc hmi hblock hcof
      (lateLinkedHlink_of_chain_C11SL S W)⟩

/-- **HCOF 版组装**：`hcof` 由 outer 的共尾 request `hCof` 给（`hcof_of_cofinal_request_C11HC`），
`W` 的 `εcut Dcut mcut` 取 `preparedSpatialPhysicalQualityRequest request n (rNext n)`。其余前提同
`linkedPackage_of_chain_C11GT3`；这里只出 S14 一半（S10 一半同上，与 `hcof` 无关）。 -/
theorem lateLinked_of_cofinal_request_C11GT3 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pB Γ P g)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ) (rNext : ℕ → ℝ)
    (hCof : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
      let req := request Aact E rTerm qDeriv ρ
      req.1 ≤ (E + 1)⁻¹ ∧ E ≤ req.2.1 ∧ E ≤ (req.2.2.1 : ℝ))
    (hrNext : ∀ n, 0 < rNext n)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (preparedSpatialPhysicalQualityRequest request n (rNext n)).1
      (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.1
      (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.2.1)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (hfixed : q.fixed = pB.fixed) (hrc : q.recenterConstant = pB.recenterConstant)
    (hmi : ∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) (n : ℕ),
      (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ≤ (n : ℝ) →
      ∃ j : Fin (F.tower.history n).eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        HEq (records n j).delta ((W m).fineRecords i).delta ∧
        HEq (records n j).order ((W m).fineRecords i).order ∧
        HEq (records n j).neck ((W m).fineRecords i).neck)
    (hblock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
      ∃ m : ℕ, ∃ i : Fin (S.state (m + 1)).native.eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ≤ (3 : ℝ) ^ m ∧
        MetricCutCapEvent.SamePresentation
          (translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent
          ((F.tower.history n).toHistory.event j) ∧
        ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
          ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
            (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
              (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
              (W m).fineParameters.modelAccuracy b'),
            HEq b b' ∧ raw.hasCanonicalWindow ∧
            raw.delta = (((W m).fineRecords i).static b).delta ∧
            raw.order = (((W m).fineRecords i).static b).order ∧
            HEq raw.neck (((W m).fineRecords i).static b).neck ∧
            raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric) :
    LateLinkedRecordsSupply_C11E F q :=
  lateLinkedRecordsSupply_of_astra_C12X S W F q records hfixed hrc hmi hblock
    (hcof_of_cofinal_request_C11HC S request rNext hCof hrNext W)
    (lateLinkedHlink_of_chain_C11SL S W)

/-- consumer：`hlinkfine_of_chain_C11GT3` 就是 v2 顶层定理 `hlinkfine` binder 的类型（逐字）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g), LinkedAndFine_C11GT2 S :=
  fun S => hlinkfine_of_chain_C11GT3 S

/-- consumer：同一个 `hlinkfine_of_chain_C11GT3 S` 的两个字段喂 S10（`a12Enhanced_of_chain_C11P2` 的 hext
项）与 S14（retention 族的 fine static caps 晚期 linked，P5L `hlink`）。 -/
example {pB : CutoffParameters} {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pB Γ P g)
    {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b) :=
  (hlinkfine_of_chain_C11GT3 S).hfine_S14 W

end GC.LongTime.Ch11
