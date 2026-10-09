import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention

set_option autoImplicit false

/-!
# O-C12X-S10A G5：S10 `LinkedWindowsSupply_C11E` 与 P5L `hlink` 的消费端（后缀 `_C12X`）

S10 修补的 ch8 侧（`docs/geometrization/chapter8/out/CH12X-S10-HORN-SPEC.md`）在 static cap 的
出生点产出 `hasLinkedCanonicalWindow_C12X`（`Surgery/Topology/LinkedCanonicalWindowC12X`，体与 ch11
`linkedCanonicalWindow_C11E` 逐字相同），并作为 `windows` 旁的不变量往下穿：
`PreparedSpatialState.linked`、`ScaffoldState.linked`、`PreparedSpatialStepRetention.fineLinked`；
narrow tuple 出口为 `hlink : ∀ n i b, ((records n i).static b).hasLinkedCanonicalWindow_C12X`。
本文件以这些出口为**显式前提**：

* `hasLinkedCanonicalWindow_C12X_iff_C11E`：两边是同一个体（`Iff.rfl`）；
* `linkedWindowsSupply_of_hlink_C12X`：narrow tuple 的 `hlink` ⇒ `LinkedWindowsSupply_C11E records`
  （`a12Enhanced_of_chain_C11P2` 的 hext 合取项逐字）；
* `lateLinkedHlink_of_fineLinked_C12X`：retention 族的 `fineLinked`（全体 block）⇒
  `lateLinkedRecordsSupply_of_outer_C12X` 的 `hlink` 前提逐字（`k₁ = 0`）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- ch8 的 linked 谓词与 ch11 的 `linkedCanonicalWindow_C11E` 是同一个体。 -/
theorem hasLinkedCanonicalWindow_C12X_iff_C11E {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.RetainedBoundaryIndex} {S : E.PresentedStaticCap fixed D m ε b} :
    S.hasLinkedCanonicalWindow_C12X ↔ linkedCanonicalWindow_C11E S :=
  Iff.rfl

/-- **S10**：narrow tuple 的出口 `hlink`（每个 record 的每个 static cap 有 linked canonical window）
给出 `LinkedWindowsSupply_C11E records`。 -/
theorem linkedWindowsSupply_of_hlink_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hlink : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      ((records n i).static b).hasLinkedCanonicalWindow_C12X) :
    LinkedWindowsSupply_C11E records :=
  hlink

/-- **P5L `hlink`**：retention 族每个 block 的 fine static caps 都 linked（`fineLinked` 字段）⇒
`lateLinkedRecordsSupply_of_outer_C12X` 的 `hlink` 前提（取 `k₁ = 0`）。 -/
theorem lateLinkedHlink_of_fineLinked_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, GC.GeneralFlow.PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hfine : ∀ k (i : Fin (S.state (k + 1)).native.eventCount) b,
      (((W k).fineRecords i).static b).hasLinkedCanonicalWindow_C12X) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b) :=
  ⟨0, fun k _ i b => hfine k i b⟩

end GC.LongTime.Ch11
