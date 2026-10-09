import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfP6C11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SupplyFourOfClosedBirthC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgeryDecay

set_option autoImplicit false

/-!
# O-CH11-ASM (G6)：W1 ⇐ 已落地的 astra narrow tuple；A12 ⇐ `PreparedSpatialChain` + S8

astra narrow tuple
`GC.GeneralFlow.PreparedSpatialChain.exists_surgery_with_spatial_control_and_decay`
（`SH/PreparedSpatialSurgeryDecay`，S-CH11-FIX6 G2：PortC11P + 原路径 shim；陈述与 ch11src 逐字同）
现在可以 import。于是：

* `w1_of_preparedSpatialChain_C11A S`：任一 `S : PreparedSpatialChain pBase C P g` 给出 G3 的 W1
  （十个合取项），另带两条"F 来自 S"的记账：`F.tower = S.tower`、`q.delta` 在 `[0, ∞)` 上等于
  `S` 的对角 accuracy；S4 用 G5 的 `canonicalConstantsSupply_of_closedBirthConstants_C11A C`。
* `largerBallScalarLarge_congr_C11A`：S8 只读 δ 在 `[0, ∞)` 上的值（树内）。
* `exists_surgery_with_decaying_accuracy_of_chain_C11A S hP6`：A12 结论逐字；`hP6` 是 **S 自己的
  tower** 与 **S 的对角 δ** 上的 S8（design §3：S8 只对构造出来的 flow 陈述）。

剩余前提：`S` 的存在（astra outer tuple，仍未落地）+ S8（P6 车道）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- `S` 的对角 accuracy 参数
（astra `CutoffParameters.diagonal (fun n => (S.observation n).parameters)`）。 -/
abbrev chainDiagonal_C11A {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) : CutoffParameters :=
  CutoffParameters.diagonal fun n => (S.observation n).parameters

/-- **W1 ⇐ narrow tuple**：任一 `PreparedSpatialChain` 给出 G3 `hflow` 的十个 W1 合取项，
外加 `F.tower = S.tower` 与 `q.delta = (chainDiagonal_C11A S).delta`（在 `[0, ∞)` 上）。 -/
theorem w1_of_preparedSpatialChain_C11A {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      F.tower = S.tower ∧ (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t) ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records := by
  obtain ⟨F, q, κ, records, hTower, -, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin, hnc,
    -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  refine ⟨F, q, κ, records, C.epsilon, max C.C1s C.Cbirth,
    max C.C2s (max C.Cbirth (C.Cgrad : ℝ)), hTower, fun t ht => ?_,
    canonicalConstantsSupply_of_closedBirthConstants_C11A C, hκ, hκanti, hδanti, hρanti,
    hcan, hwin, hnc, hδlim, hrecent⟩
  change q.delta t = ((S.observation (Nat.ceil t)).parameters).delta t
  exact (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).1

/-- 树内：S8 只读 δ 在 `[0, ∞)` 上的值（accuracy 前提里 `s ≥ t/2 ≥ 0`，对角 α 的自变量 `≥ 0`）。 -/
theorem largerBallScalarLarge_congr_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ δ' : ℝ → ℝ} (hδ : ∀ t : ℝ, 0 ≤ t → δ t = δ' t)
    (h : LargerBallScalarLargeSupply_C11S F δ' (diagonalAccuracy_C11S δ')) :
    LargerBallScalarLargeSupply_C11S F δ (diagonalAccuracy_C11S δ) := by
  intro A hA
  obtain ⟨rbar, K, hrbar, hK, hmain⟩ := h A hA
  refine ⟨rbar, K, hrbar, hK, fun n t p r hr hacc => hmain n t p r hr fun s hs => ?_⟩
  have hs0 : 0 ≤ s := le_trans (div_nonneg t.2.1 zero_le_two) hs.1
  have hacc' := hacc s hs
  change δ s < 2 * δ (max 0 (A / 4)) at hacc'
  change δ' s < 2 * δ' (max 0 (A / 4))
  rw [← hδ s hs0, ← hδ _ (le_max_left _ _)]
  exact hacc'

/-- **A12 ⇐ `PreparedSpatialChain` + S8**（G6 主定理）：S8 陈述在 `S` 自己的 tower 与对角 δ 上。 -/
theorem exists_surgery_with_decaying_accuracy_of_chain_C11A {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (hP6 : ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
      LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
        (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ := by
  obtain ⟨F, q, κ, records, ε, C1, C2, hTower, hq, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    hwin, hnc, hδlim, hrecent⟩ := w1_of_preparedSpatialChain_C11A S
  exact exists_surgery_with_decaying_accuracy_of_P6_C11A P g
    ⟨F, q, κ, records, ε, C1, C2, hconst, hκ, hκanti, hδanti, hρanti, hcan, hwin, hnc, hδlim,
      hrecent, largerBallScalarLarge_congr_C11A hq (hP6 F hTower)⟩

/-- **P g 层**：存在某个 chain 且其 tower 上 S8 成立 ⇒ A12（结论逐字）。 -/
theorem exists_surgery_with_decaying_accuracy_of_someChain_C11A
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : ∃ (pBase : CutoffParameters) (C : GC.GeneralFlow.ClosedBirthConstants)
      (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g),
      ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ := by
  obtain ⟨pBase, C, S, hP6⟩ := h
  exact exists_surgery_with_decaying_accuracy_of_chain_C11A S hP6

/-- 逐字对齐：结论类型就是 A12 的类型。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : ∃ (pBase : CutoffParameters) (C : GC.GeneralFlow.ClosedBirthConstants)
      (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g),
      ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_someChain_C11A P g h

/-- consumer：任一 chain 同时给出 SKEL bundle 的 S1–S7、S9（不需要 S8）。 -/
example {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      AccuracyDecaySupply_C11S q.delta ∧ RadiusAntitoneSupply_C11S q ∧
      CanonicalWindowsSupply_C11S records ∧ CanonicalConstantsSupply_C11S ε C1 C2 ∧
      CanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧ NoncollapseSupply_C11S F κ ε ∧
      LargerBallAccuracySupply_C11S q.delta (diagonalAccuracy_C11S q.delta) ∧
      RecentCutoffSupply_C11S records := by
  obtain ⟨F, q, κ, records, ε, C1, C2, -, -, hconst, hκ, hκanti, hδanti, hρanti, hcan, hwin,
    hnc, hδlim, hrecent⟩ := w1_of_preparedSpatialChain_C11A S
  exact ⟨F, q, κ, records, ε, C1, C2, supplies_of_astra_C11A F q κ records ε C1 C2 hconst hκ
    hκanti hδanti hρanti hcan hwin hnc hδlim hrecent⟩

end GC.LongTime.Ch11
