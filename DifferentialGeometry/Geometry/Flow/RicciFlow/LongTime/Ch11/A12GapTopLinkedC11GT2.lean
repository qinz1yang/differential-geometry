import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S

set_option autoImplicit false

/-!
# S-CH11-GAPTOP2 G5：`hlinkS10` 与 `hfine_S14` 合并为一个 binder（后缀 `_C11GT2`）

R-C11-6 D-14（Q5(c)）：`hlinkS10` 与顶层 `hfine`（S14）是**同一个实际插帽（insertion）的 high-order /
link certificate** 在粗 records 与 retained fine records 上的两个出口，应由**同一个 insertion producer +
transport** 一起交付；`hpbase` 的 collar 条是这条构造链的上游条件，但不与它们混成一个小引理。
`hP6b`/`hspine`、`hK`、`hfull` 仍各自独立（D-14 的其余几句）。

* `LinkedAndFine_C11GT2 S`（Prop 值结构，lead 授权）：对 chain `S`，两个字段
  * `hlinkS10`：S10——对 `S` 的任意 tuple `(F, q, records)`（`F.tower = S.tower`、静态参数等式、
    `records` 与 `S.observation` 的逐字段 `HEq` bridge），`LinkedWindowsSupply_C11E records`。
    **形与 S10HORN 的 `linkedWindowsSupply_of_chain_C11SL` 逐字同**（`hstatic` + 五项 `hbridge`），
    比 GT 版 `hlinkS10`（只给 static 的 `HEq`）多给 producer 两个前提，故是更弱的 binder；
  * `hfine_S14`：S14——任意 retention 族 `W` 的 fine static caps 晚期 linked，**形与 P5L 的 `hlink`
    （`lateLinkedRecordsSupply_of_outer_C12X`）逐字同**（`∃ k₁, ∀ k ≥ k₁, …`），
    比 GT 版 `hfine`（全 block `hasLinkedCanonicalWindow_C12X`）更弱；S10HORN 的
    `lateLinkedHlink_of_chain_C11SL`（`fineLinked` 字段 ⇒ 本字段）就是 producer。
  **它不是 κ 内部的 `hfine_K3`（`KappaFineScale_C11Q5`）**：后者是另一个义务，在 `hK` 的 producer 内
  （R-C11-6 D-13(2)：`hfine_S14` 是 `hasLinkedCanonicalWindow` 供给，不含整个 quotient 上的 `hact`）。
* `LinkedAndFine_C11GT2.of_fineLinked_C11GT2`：由 S10 出口 + 全 block 的 `fineLinked` 形（S10HORN 的
  `PreparedSpatialStepRetention.fineLinked`）构造结构（经树内 `lateLinkedHlink_of_fineLinked_C12X`），
  即两个出口确实来自同一组 insertion 数据。
* 无条件 inhabitant：目前没有（缺口本身 = S10HORN 落树前的 S10 / S14）；结构既不强于也不弱于"两个
  binder 之并"（`⟨h₁, h₂⟩` / 两个投影），见 `linkedAndFine_iff_C11GT2`。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

/-- **S10 + S14 的合并出口**（同一个 insertion producer + transport）：chain `S` 上
`hlinkS10`（粗 records 的 linked，S10HORN `linkedWindowsSupply_of_chain_C11SL` 形）与
`hfine_S14`（retention 族的 fine static caps 晚期 linked，P5L `hlink` 形）。 -/
structure LinkedAndFine_C11GT2 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pB Γ P g) : Prop where
  hlinkS10 : ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q), F.tower = S.tower →
    (q.fixed = pB.fixed ∧ q.modelRadius = pB.modelRadius ∧ q.modelOrder = pB.modelOrder ∧
      q.modelAccuracy = pB.modelAccuracy ∧ q.recenterConstant = pB.recenterConstant) →
    (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) →
    LinkedWindowsSupply_C11E records
  hfine_S14 : ∀ {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)),
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b)

/-- 构造：S10 出口 + 全 block 的 `fineLinked` 形（`hasLinkedCanonicalWindow_C12X`，S10HORN 的
`PreparedSpatialStepRetention.fineLinked` 字段的形）⇒ `LinkedAndFine_C11GT2 S`。
S14 出口经树内 `lateLinkedHlink_of_fineLinked_C12X`（取 `k₁ = 0`）。 -/
theorem LinkedAndFine_C11GT2.of_fineLinked_C11GT2 {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {S : PreparedSpatialChain pB Γ P g}
    (hS10 : ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : CutoffRecords_C11S F q), F.tower = S.tower →
      (q.fixed = pB.fixed ∧ q.modelRadius = pB.modelRadius ∧ q.modelOrder = pB.modelOrder ∧
        q.modelAccuracy = pB.modelAccuracy ∧ q.recenterConstant = pB.recenterConstant) →
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
          HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
          HEq (records n i).delta ((S.observation n).records j).delta ∧
          HEq (records n i).order ((S.observation n).records j).order ∧
          HEq (records n i).neck ((S.observation n).records j).neck ∧
          HEq (records n i).static ((S.observation n).records j).static) →
      LinkedWindowsSupply_C11E records)
    (hfine : ∀ {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
      (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
        (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)),
      ∀ k (i : Fin (S.state (k + 1)).native.eventCount) b,
        (((W k).fineRecords i).static b).hasLinkedCanonicalWindow_C12X) :
    LinkedAndFine_C11GT2 S :=
  ⟨hS10, fun W => lateLinkedHlink_of_fineLinked_C12X S W (hfine W)⟩

/-- 结构不强于 / 不弱于"两个 binder 之并"（对全体 chain 逐点）：`LinkedAndFine_C11GT2 S` 恰好是
S10 出口与 S14 出口的合取。 -/
theorem linkedAndFine_iff_C11GT2 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {S : PreparedSpatialChain pB Γ P g} :
    LinkedAndFine_C11GT2 S ↔
      ((∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
        (records : CutoffRecords_C11S F q), F.tower = S.tower →
        (q.fixed = pB.fixed ∧ q.modelRadius = pB.modelRadius ∧ q.modelOrder = pB.modelOrder ∧
          q.modelAccuracy = pB.modelAccuracy ∧ q.recenterConstant = pB.recenterConstant) →
        (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
          (j : Fin (S.observation n).history.eventCount), i.val = j.val →
            HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
            HEq (records n i).delta ((S.observation n).records j).delta ∧
            HEq (records n i).order ((S.observation n).records j).order ∧
            HEq (records n i).neck ((S.observation n).records j).neck ∧
            HEq (records n i).static ((S.observation n).records j).static) →
        LinkedWindowsSupply_C11E records) ∧
      (∀ {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
        (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
          (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)),
        ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
          linkedCanonicalWindow_C11E (((W k).fineRecords i).static b))) :=
  ⟨fun h => ⟨h.hlinkS10, h.hfine_S14⟩, fun h => ⟨h.1, h.2⟩⟩

/-- consumer：同一个 `LinkedAndFine_C11GT2 S` 同时喂 S10（`LinkedWindowsSupply_C11E records`，
`a12Enhanced_of_chain_C11P2` 的 hext S10 项）与 S14（`lateLinkedRecordsSupply_of_outer_C12X` 的 `hlink`）；
retention 的 fine static caps 晚期 linked 即 P5L `hlink`。 -/
example {pB : CutoffParameters} {Γ : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} {S : PreparedSpatialChain pB Γ P g} (h : LinkedAndFine_C11GT2 S)
    {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n)) :
    ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b) :=
  h.hfine_S14 W

end GC.LongTime.Ch11
