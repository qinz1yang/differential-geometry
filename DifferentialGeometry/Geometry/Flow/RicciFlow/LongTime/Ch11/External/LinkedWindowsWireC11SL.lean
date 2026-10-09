import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedWindowTransportC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDecay

set_option autoImplicit false

/-!
# S-CH11-S10HORN G3：narrow tuple 出口 `hlink` 与 S10 / P5L 的接线（后缀 `_C11SL`）

ch8 侧的 S10 修补在 static cap 的出生点（`HornFineCutoffRecordDistanceC11X`）产出
`hasLinkedCanonicalWindow_C12X`，沿 Distance 链并槽位下穿，并作为不变量 `linked`
（`PreparedSpatialState` / `ScaffoldState`）与 `fineLinked`（`PreparedSpatialStepRetention`）
落到 chain 上。narrow tuple 本身**不改**：它已经带有 bridge 项
`HEq (records n i).static ((S.observation n).records j).static`，
所以 tuple 的 `records` 的 `hlink` 由 bridge + `(S.observation n).linked` 经 `family_heq`
镜像给出（与 tuple 里 `hwin` 的证明同形）。

* `hlink_of_narrowTuple_C11SL`：`hlink`；
* `linkedWindowsSupply_of_chain_C11SL`：⇒ `LinkedWindowsSupply_C11E records`
  （`a12Enhanced_of_chain_C11P2` 的 hext S10 项，经 S10A 的 `linkedWindowsSupply_of_hlink_C12X`）；
* `lateLinkedHlink_of_chain_C11SL`：retention 族 ⇒ P5L 的 `hlink`（S14，同形）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- narrow tuple 的出口：tuple 的 `records` 每个 static cap 都 linked。
`hstatic`、`hbridge` 取自 `exists_surgery_with_spatial_control_and_decay` 的同名合取项。 -/
theorem hlink_of_narrowTuple_C11SL {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hTower : F.tower = S.tower)
    (hstatic : q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
      q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
      q.recenterConstant = pBase.recenterConstant)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) :
    ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      ((records n i).static b).hasLinkedCanonicalWindow_C12X := by
  rcases F with ⟨K, hcontrol⟩
  change K = S.tower at hTower
  subst hTower
  intro n i
  have hs := (S.observation n).static_eq
  exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
    rfl rfl rfl rfl HEq.rfl (hstatic.1.trans hs.1.symm) (hstatic.2.1.trans hs.2.1.symm)
    (hstatic.2.2.1.trans hs.2.2.1.symm) (hstatic.2.2.2.1.trans hs.2.2.2.1.symm)
    ((S.observation n).records i).static (records n i).static (hbridge n i i rfl).2.2.2.2
    ((S.observation n).linked i)

/-- **S10**：narrow tuple ⇒ `LinkedWindowsSupply_C11E records`。 -/
theorem linkedWindowsSupply_of_chain_C11SL {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hTower : F.tower = S.tower)
    (hstatic : q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
      q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
      q.recenterConstant = pBase.recenterConstant)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) :
    LinkedWindowsSupply_C11E records :=
  linkedWindowsSupply_of_hlink_C12X records
    (hlink_of_narrowTuple_C11SL S F q records hTower hstatic hbridge)

/-- **S14（P5L）`hlink`**：`PreparedSpatialStepRetention` 族 ⇒ `lateLinkedRecordsSupply_of_outer_C12X`
的 `hlink` 前提（`fineLinked` 字段，同形）。 -/
theorem lateLinkedHlink_of_chain_C11SL {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, GC.GeneralFlow.PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b) :=
  lateLinkedHlink_of_fineLinked_C12X S W fun k i b => (W k).fineLinked i b

/-- consumer：从同一个 narrow tuple 投影出 tower equality、canonical windows，
并为同一 `records` 补上 `LinkedWindowsSupply_C11E records`。
其余 W1 合取项仍由原 `exists_surgery_with_spatial_control_and_decay` 提供。 -/
theorem narrowTuple_with_linkedWindows_C11SL {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : ∀ n (i : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      F.tower = S.tower ∧ (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      LinkedWindowsSupply_C11E records := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, hbridge, hcan,
    hwin, hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  exact ⟨F, q, records, hTower, hwin,
    linkedWindowsSupply_of_chain_C11SL S F q records hTower hstatic hbridge⟩

end GC.LongTime.Ch11
