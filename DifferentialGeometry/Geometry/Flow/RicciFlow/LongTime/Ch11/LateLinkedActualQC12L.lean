import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilOfOuterSupplyP6HC2

set_option autoImplicit false

/-!
# C12-10：S14 `LateLinkedRecordsSupply` 在 SCRS⁺ 的实际 `F₀ q₀` 上（后缀 `_C12L`）

`SameConstructionRetentionSupplyPlus_C11GT6 T`（`A12GapTopV6FwdC11GT6.lean` l.111）的第 (5) 组已含
`LateLinkedRecordsSupply_C11E F₀ q₀`（hcof 由 outer 的 `hCof` + `hcof_of_cofinal_request_C11HC`、
hlink 由 `fineLinked` + `lateLinkedHlink_of_chain_C11SL` 在 producer 里付清）。所以 `q = q₀` 时
A12′ v9 的 `hS14` 槽就是 SCRS⁺ 的投影，不需要再接 hcof / hlink。`q ≠ q₀`（`q.fixed`、
`q.recenterConstant` 自由）无来源，见 `build-logs/resume/state-C12-10.md`。
`p.delta = q₀.delta` 是 SCRS⁺ 给的全轴函数等式，t ≥ 0 与全实轴的差别自动消失。

* `hS14_at_q0_of_scrsPlus_C12L`：SCRS⁺ ⇒ ∃ `F q`，v9 `hS14` 槽的全部前提（`F.tower`、`hq`、
  `hstatic`）与结论 `LateLinkedRecordsSupply_C11E F q`；
* `example`：该输出喂 `lateRecords_of_S14_P6SS` / `hrec_of_lateRecords_P6SS`（HCEIL 消费端同形）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **S14 在 `q₀` 上**：SCRS⁺ ⇒ 实际 `F q`（= SCRS⁺ 的 `F₀ q₀`）满足 v9 `hS14` 槽的前提，
并且 `LateLinkedRecordsSupply_C11E F q`。 -/
theorem hS14_at_q0_of_scrsPlus_C12L {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (q.fixed = pB.fixed ∧ q.modelRadius = pB.modelRadius ∧
        q.modelOrder = pB.modelOrder ∧ q.modelAccuracy = pB.modelAccuracy ∧
        q.recenterConstant = pB.recenterConstant) ∧
      LateLinkedRecordsSupply_C11E F q := by
  obtain ⟨F₀, q₀, -, -, ⟨h1, h2, h3⟩, -, -, -, ⟨-, -, -, h4⟩, -⟩ := hS
  exact ⟨F₀, q₀, h1, h2, h3, h4⟩

/-- **consumer**：`q₀` 处的 `hS14` 喂 S14 投影 `lateRecords_of_S14_P6SS` / `hrec_of_lateRecords_P6SS`。 -/
example {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) : True := by
  obtain ⟨F, q, -, -, -, hS14⟩ := hS14_at_q0_of_scrsPlus_C12L hS
  have := ObservedHistory.hrec_of_lateRecords_P6SS (ObservedHistory.lateRecords_of_S14_P6SS hS14)
  trivial

end GC.LongTime.Ch11
