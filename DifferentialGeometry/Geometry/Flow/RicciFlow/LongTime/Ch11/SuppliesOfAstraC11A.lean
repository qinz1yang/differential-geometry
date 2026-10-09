import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S

set_option autoImplicit false

/-!
# O-CH11-ASM (G2)：从 astra spatial tuple 的结论形逐个 discharge S1–S7、S9

astra 的 producer 是**一个**存在定理：narrow tuple `exists_surgery_with_spatial_control_and_decay`
（ch11src `SH/PreparedSpatialSurgeryDecay.lean:55`，输入 `S : PreparedSpatialChain`）⇐ outer tuple
`…_with_closed_support_and_window_scale_bound`（`SH/PreparedSpatialPhysicalVolumeEvent.lean:33`）。
二者的 import 闭包都含 `CutoffRecordSplicing`（FAIL）、`PresentedStaticCapRestriction`（FAIL）、
`CutoffRecordConcatenation`（SKIP）⇒ 按用户 21:4x 裁定**永久 reference-only**，不 import。

所以这里把 narrow tuple 的结论（去掉 `S`-专属的 HEq 桥 / prefix 条款，`ε := C.epsilon`、
`C1 := max C.C1s C.Cbirth`、`C2 := max C.C2s (max C.Cbirth Cgrad)`）当作**显式 binder**（下称 W1），
每个供给 `S_k` 由 W1 的对应合取项经 ≤ 20 行 adapter 得到（`supply_k_of_astra_C11A`）。
W1 的每个 binder 都逐字取自 astra 陈述，只用树内类型；S8（A > 1）不在这里。

* S1 ⇐ `AntitoneOn q.delta (Ici 0)` + `Tendsto q.delta atTop (𝓝 0)`（tuple 两项）；
* S2 ⇐ `AntitoneOn q.neckRadius (Ici 0)`；S3 ⇐ canonical windows（逐字）；
* S4 ⇐ `ClosedBirthConstants` 的字段（`epsilon_pos / epsilon_small / C1s_ge_one / C2s_ge_one`）
  + tuple 的 `max` 组合（`Cbirth`、`Cgrad` 任意实数；`Cbirth_ge_one` 用不到）；
* S5 ⇐ history 形 canonical（`canonicalSupply_of_history_C11S`）；
* S6 ⇐ `∀ t, 0 < κ t`、`Antitone κ`、`∀ n, ∀ t ∈ [0, n], NoncollapsedBefore (κ t) ε t`（取 `t = n`）；
* S7 ⇐ 对角 accuracy `diagonalAccuracy_C11S q.delta`（只用 S1 的 antitone；= astra
  `diagonalLargerBallAccuracy`，`SH/PreparedSpatialLargerBallAccuracy.lean:33`）；
* S9 ⇐ recent-cutoff 条款（逐字，`η` 量词）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- **S1** ⇐ tuple 的 `AntitoneOn q.delta (Ici 0)` 与 `Tendsto q.delta atTop (𝓝 0)`。 -/
theorem supply1_of_astra_C11A (q : CutoffParameters)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hδlim : Tendsto q.delta atTop (𝓝 0)) :
    AccuracyDecaySupply_C11S q.delta :=
  accuracyDecaySupply_of_tendsto_C11S hδanti hδlim

/-- **S2** ⇐ tuple 的 `AntitoneOn q.neckRadius (Ici 0)`（逐字）。 -/
theorem supply2_of_astra_C11A (q : CutoffParameters)
    (hρanti : AntitoneOn q.neckRadius (Ici 0)) : RadiusAntitoneSupply_C11S q :=
  hρanti

/-- **S3** ⇐ tuple 的 canonical windows 条款（逐字）。 -/
theorem supply3_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow) :
    CanonicalWindowsSupply_C11S records :=
  hwin

/-- **S4** ⇐ `ClosedBirthConstants` 的字段与 tuple 的 `max` 组合：
`ε = C.epsilon`、`C1 = max C.C1s C.Cbirth`、`C2 = max C.C2s (max C.Cbirth Cgrad)`。 -/
theorem supply4_of_astra_C11A {ε C1s C2s Cbirth : ℝ} (Cgrad : ℝ)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hC1s : 1 ≤ C1s) (hC2s : 1 ≤ C2s) :
    CanonicalConstantsSupply_C11S ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) :=
  ⟨hε, hεsmall, hC1s.trans (le_max_left _ _), hC2s.trans (le_max_left _ _)⟩

/-- **S5** ⇐ tuple 的 history 形 canonical witness（`n = ⌈t⌉` 上读 `postMetric`）。 -/
theorem supply5_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (ε C1 C2 : ℝ)
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2) :
    CanonicalSupply_C11S F q.neckRadius ε C1 C2 :=
  canonicalSupply_of_history_C11S F q.neckRadius ε C1 C2 hcan

/-- **S6** ⇐ tuple 的 `∀ t, 0 < κ t`、`Antitone κ` 与 `[0, n]` 上的 noncollapse（取 `t = n`）。 -/
theorem supply6_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (κ : ℝ → ℝ) (ε : ℝ)
    (hκ : ∀ t : ℝ, 0 < κ t) (hκanti : Antitone κ)
    (hnc : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t) ε t) :
    NoncollapseSupply_C11S F κ ε := by
  refine ⟨fun t _ => hκ t, fun s _ t _ hst => hκanti hst, fun n => ?_⟩
  exact hnc n (n : ℝ) ⟨Nat.cast_nonneg n, le_rfl⟩

/-- **S7** ⇐ S1 的 antitone：对角 accuracy（astra `diagonalLargerBallAccuracy` 同式）。 -/
theorem supply7_of_astra_C11A (q : CutoffParameters) (hδanti : AntitoneOn q.delta (Ici 0)) :
    LargerBallAccuracySupply_C11S q.delta (diagonalAccuracy_C11S q.delta) :=
  largerBallAccuracySupply_diagonal_C11S q hδanti

/-- **S9** ⇐ tuple 的 recent-cutoff 条款（逐字，量词名 `η`）。 -/
theorem supply9_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q)
    (hrecent : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
      ∀ i : Fin (F.tower.history n).eventCount,
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t) :
    RecentCutoffSupply_C11S records :=
  hrecent

/-- **S1–S7、S9 合并**：W1 的合取项（逐字）⇒ 除 S8 外的全部供给，α 取对角。 -/
theorem supplies_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hrecent : RecentCutoffSupply_C11S records) :
    AccuracyDecaySupply_C11S q.delta ∧ RadiusAntitoneSupply_C11S q ∧
      CanonicalWindowsSupply_C11S records ∧ CanonicalConstantsSupply_C11S ε C1 C2 ∧
      CanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧ NoncollapseSupply_C11S F κ ε ∧
      LargerBallAccuracySupply_C11S q.delta (diagonalAccuracy_C11S q.delta) ∧
      RecentCutoffSupply_C11S records :=
  ⟨supply1_of_astra_C11A q hδanti hδlim, supply2_of_astra_C11A q hρanti,
    supply3_of_astra_C11A records hwin, hconst,
    supply5_of_astra_C11A F q ε C1 C2 hcan, supply6_of_astra_C11A F κ ε hκ hκanti hnc,
    supply7_of_astra_C11A q hδanti, supply9_of_astra_C11A records hrecent⟩

/-- **bundle**：W1 的合取项 + S8（对角 α）⇒ SKEL 的 `SurgerySupplies_C11S`。 -/
theorem surgerySupplies_of_astra_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)) :
    SurgerySupplies_C11S P g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩ := supplies_of_astra_C11A F q κ records ε C1 C2
    hconst hκ hκanti hδanti hρanti hcan hwin hnc hδlim hrecent
  exact ⟨F, q, records, ε, C1, C2, κ, diagonalAccuracy_C11S q.delta,
    h1, h2, h3, h4, h5, h6, h7, hLB, h9⟩

/-- consumer（S4 的数值实例）：常数 `ε = 1/200`、`C1s = C2s = Cbirth = 1`、`Cgrad = 0` 满足 S4。 -/
example : CanonicalConstantsSupply_C11S (1 / 200) (max 1 1) (max 1 (max 1 0)) :=
  supply4_of_astra_C11A 0 (by norm_num) (by norm_num) le_rfl le_rfl

end GC.LongTime.Ch11
