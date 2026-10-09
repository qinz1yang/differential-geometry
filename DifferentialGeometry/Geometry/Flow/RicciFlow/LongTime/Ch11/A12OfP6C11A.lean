import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SuppliesOfAstraC11A

set_option autoImplicit false

/-!
# O-CH11-ASM (G3)：A12 归约到 W1 + S8（P6 / KL 84.1(c) 的 A > 1）

`exists_surgery_with_decaying_accuracy_of_P6_C11A` 的结论与 A12
（`GC.LongTime.exists_surgery_with_decaying_accuracy`）**逐字相同**（`type_of%` 的 `example`）。
前提只有一个 `∃`：同一组数据 `(F, q, κ, records, ε, C1, C2)` 上
* **W1**（等待项，producer = astra narrow tuple `exists_surgery_with_spatial_control_and_decay`
  ⇐ outer tuple，ch11src `SH/PreparedSpatialSurgeryDecay.lean:55` /
  `SH/PreparedSpatialPhysicalVolumeEvent.lean:33`，闭包含 FAIL 模块 ⇒ reference-only）：
  tuple 结论去掉 `S`-专属条款后的十个合取项，逐字；
* **S8** `LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)`（P6 车道）。

为什么 S8 与 W1 绑在同一个 `∃` 里而不是写成 `∀ F, W1 → S8`：α 取对角
`2 δ(max 0 (A/4))` 时，S8 的 accuracy 前提 `δ s < α A s` 只在 δ 逐块下跌时才编码
"`A ≲ t`"；astra 用 outer tuple 的 `request` / block 条款（`δ s < diagAcc A s → A < 12·3^m`，
`SH/PreparedSpatialPhysicalVolumeEvent.lean:343–353`）保证这一点，而这些条款**不在** W1 里。
所以 S8 是关于**构造出来的那个** F 的陈述，不是对一切满足 W1 的 flow 的陈述。
另给数据显式版（S32 式 binder）与 α 由 P6 自选的变体 `…_of_P6_data_flex_C11A`。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- **A12（数据显式版，α 由 P6 自选）**：W1 的合取项 + 任意满足 S7 的 α 上的 S8。 -/
theorem exists_surgery_with_decaying_accuracy_of_P6_data_flex_C11A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
    (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hκ : ∀ t : ℝ, 0 < κ t) (hκanti : Antitone κ)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hnc : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t) ε t)
    (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hrecent : RecentCutoffSupply_C11S records)
    (α : ℝ → ℝ → ℝ) (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hP6 : LargerBallScalarLargeSupply_C11S F q.delta α) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_data_C11S F q records ε C1 C2 κ α
    (supply1_of_astra_C11A q hδanti hδlim) (supply2_of_astra_C11A q hρanti)
    (supply3_of_astra_C11A records hwin) hconst (supply5_of_astra_C11A F q ε C1 C2 hcan)
    (supply6_of_astra_C11A F κ ε hκ hκanti hnc) hacc hP6
    (supply9_of_astra_C11A records hrecent)

/-- **A12（数据显式版）**：W1 的合取项 + 对角 α 上的 S8；S7 树内。 -/
theorem exists_surgery_with_decaying_accuracy_of_P6_data_C11A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
    (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hκ : ∀ t : ℝ, 0 < κ t) (hκanti : Antitone κ)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hnc : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t) ε t)
    (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hrecent : RecentCutoffSupply_C11S records)
    (hP6 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_P6_data_flex_C11A F q κ records ε C1 C2 hconst
    hκ hκanti hδanti hρanti hcan hwin hnc hδlim hrecent _ (supply7_of_astra_C11A q hδanti) hP6

/-- **A12 ⇐ W1 + S8**（O-CH11-ASM G3 主定理）。前提 `hflow` 的十个合取项 = astra narrow tuple
结论（等待项，见文件头），最后一项 = S8（P6 车道）。结论与 A12 逐字相同，0 sorry。 -/
theorem exists_surgery_with_decaying_accuracy_of_P6_C11A
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hflow : ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ := by
  obtain ⟨F, q, κ, records, ε, C1, C2, hconst, hκ, hκanti, hδanti, hρanti, hcan, hwin, hnc,
    hδlim, hrecent, hP6⟩ := hflow
  exact exists_surgery_with_decaying_accuracy_of_P6_data_C11A F q κ records ε C1 C2 hconst
    hκ hκanti hδanti hρanti hcan hwin hnc hδlim hrecent hP6

/-- 同一前提也给出 SKEL 的 bundle（两条总装路线一致）。 -/
theorem surgerySupplies_of_P6_C11A (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hflow : ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)) :
    SurgerySupplies_C11S P g := by
  obtain ⟨F, q, κ, records, ε, C1, C2, hconst, hκ, hκanti, hδanti, hρanti, hcan, hwin, hnc,
    hδlim, hrecent, hP6⟩ := hflow
  exact surgerySupplies_of_astra_C11A F q κ records ε C1 C2 hconst hκ hκanti hδanti hρanti
    hcan hwin hnc hδlim hrecent hP6

/-- 逐字对齐：主定理的结论类型就是 A12 的类型。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hflow : ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_P6_C11A P g hflow

/- The legacy admission-consuming example was retired; proved enhanced consumers live downstream. -/

-- (REPOINT2) example removed: `late_derivative_tests_of_flow` now takes
-- `hasEnhancedAdmissibility_C11E`; P6 data only yields the analytic profile

end GC.LongTime.Ch11
