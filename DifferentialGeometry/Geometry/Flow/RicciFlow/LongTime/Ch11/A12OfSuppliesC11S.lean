import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

set_option autoImplicit false

/-!
# O-CH11-SKEL (G2)：从显式供给总装 A12

纯 wiring、0 sorry：`profileOfSupplies_C11S` 用 S2–S9 与树内定理（`pinching / scalar_lower`
来自 `curvatureLower_of_records_C11S`，`larger_ball_scalar_control` 的 `A ≤ 1` 来自
`largerBallScalarAt_of_le_one_C11S`）逐字段构造 `AnalyticSurgeryProfile F q.delta`；
`exists_surgery_with_decaying_accuracy_of_supplies_C11S` 的结论与 A12
（`GC.LongTime.exists_surgery_with_decaying_accuracy`）**逐字相同**（见下方 `type_of%` 的 `example`）。

Consumers：A09 `exists_late_cut_family` 的 `hadm / hdec` 前提形（`example`；A13 自 REPOINT2
起吃 enhanced profile，其 example 已删，见 `A12EnhancedC11E`）；sorry-free 的
`commonNeckAccuracy_of_supplies_C11S`；以及
`hrc_of_decay_C11S`——ch12 残余 binder `hrc`（LOGKEEPER 记录的 ch11 候选供给）其实只由
`accuracy_eq` + decay 推出，对**任意** profile 成立。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set

namespace GC.LongTime.Ch11

universe u

/-- `pinching` 的 shift（`scalar_lower` 的 shift 是它的一半），由树内定理选出。 -/
def curvatureShift_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) : ℝ :=
  (curvatureLower_of_records_C11S F records).choose

/-- **供给 ⇒ profile**：在给定数据上逐字段构造 `AnalyticSurgeryProfile F q.delta`
（`parameters = q`、`epsilon = eps`、`kappa = κ`、`largerBallAccuracy = α` 都是 `rfl`）。 -/
def profileOfSupplies_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (hrcs : RecentCutoffSupply_C11S records) :
    AnalyticSurgeryProfile F q.delta where
  parameters := q
  accuracy_eq := rfl
  records := records
  canonical_windows := hwin
  radius_antitone := hrad
  epsilon := eps
  epsilon_pos := hconst.1
  epsilon_small := hconst.2.1
  C1 := C1
  C2 := C2
  C1_ge_one := hconst.2.2.1
  C2_ge_one := hconst.2.2.2
  canonical := hcan
  kappa := κ
  kappa_pos := hnc.1
  kappa_antitone := hnc.2.1
  noncollapsed := hnc.2.2
  scalarShift := curvatureShift_C11S F records / 2
  scalarShift_pos := half_pos (curvatureLower_of_records_C11S F records).choose_spec.1
  scalar_lower := fun t ht x =>
    ((curvatureLower_of_records_C11S F records).choose_spec.2 t ht x).2
  pinchingShift := curvatureShift_C11S F records
  pinchingShift_pos := (curvatureLower_of_records_C11S F records).choose_spec.1
  pinching := fun t ht x =>
    ((curvatureLower_of_records_C11S F records).choose_spec.2 t ht x).1
  largerBallAccuracy := α
  largerBallAccuracy_pos := hacc.1
  largerBallAccuracy_antitone_time := hacc.2.1
  largerBallAccuracy_antitone_radius := hacc.2.2.1
  diagonal_smallness := hacc.2.2.2
  larger_ball_scalar_control := largerBallScalar_of_large_C11S hLB
  recent_cutoff_smallness := hrcs

/-- **A12（数据显式版）**：S32 式写法，数据与 S1–S9 全作显式 binder。 -/
theorem exists_surgery_with_decaying_accuracy_of_data_C11S {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hδ : AccuracyDecaySupply_C11S q.delta)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (hrcs : RecentCutoffSupply_C11S records) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  ⟨q.delta, F, hδ.1, hδ.2,
    ⟨profileOfSupplies_C11S F q records eps C1 C2 κ α hrad hwin hconst hcan hnc hacc hLB hrcs⟩⟩

/-- **A12 从供给 bundle**：结论与 `exists_surgery_with_decaying_accuracy` 逐字相同，0 sorry。 -/
theorem exists_surgery_with_decaying_accuracy_of_supplies_C11S
    (P : OrientedThreeStage.{u}) (g : P.Metric) (h : SurgerySupplies_C11S P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ := by
  obtain ⟨F, q, records, eps, C1, C2, κ, α, hδ, hrad, hwin, hconst, hcan, hnc, hacc, hLB,
    hrcs⟩ := h
  exact exists_surgery_with_decaying_accuracy_of_data_C11S F q records eps C1 C2 κ α hδ hrad
    hwin hconst hcan hnc hacc hLB hrcs

/-- 逐字对齐检查：总装定理的类型就是 A12 的类型（显式保留原 A12 的陈述）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (h : SurgerySupplies_C11S P g) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_supplies_C11S P g h

/-- profile 的投影是定义等式（ch12 / O-CH11-PROF 对接用）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hrad : RadiusAntitoneSupply_C11S q) (hwin : CanonicalWindowsSupply_C11S records)
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F q.neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S q.delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F q.delta α)
    (hrcs : RecentCutoffSupply_C11S records) :
    let Hp := profileOfSupplies_C11S F q records eps C1 C2 κ α hrad hwin hconst hcan hnc
      hacc hLB hrcs
    Hp.parameters = q ∧ Hp.epsilon = eps ∧ Hp.kappa = κ ∧ Hp.largerBallAccuracy = α :=
  ⟨rfl, rfl, rfl, rfl⟩

/- The legacy admission-consuming example was retired; proved enhanced consumers live downstream. -/

-- (REPOINT2) example removed: `late_derivative_tests_of_flow` now takes
-- `hasEnhancedAdmissibility_C11E`; the supply bundle only yields the analytic profile

/-- Consumer（sorry-free）：供给 ⇒ 晚期 decay 的共同 neck accuracy。 -/
theorem commonNeckAccuracy_of_supplies_C11S (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : SurgerySupplies_C11S P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨Hp⟩⟩ := exists_surgery_with_decaying_accuracy_of_supplies_C11S P g h
  exact ⟨δ, F, hdec, Hp.commonNeckAccuracy⟩

/-- ch12 的 `hrc`（逐字 binder 形）对任意 profile 成立：`recenterConstant` 是常数而 δ → 0。 -/
theorem hrc_of_decay_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ Trc : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      Trc ≤ (F.tower.history n).toHistory.time i.succ →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2 := by
  have hrc := Hp.parameters.recenterConstant_ge_four
  obtain ⟨B, hB⟩ := hdec (1 / (2 * Hp.parameters.recenterConstant))
    (div_pos one_pos (by linarith))
  refine ⟨B + 1, fun n i hi => ?_⟩
  rw [Hp.accuracy_eq]
  have hδ := hB _ (by linarith)
  calc Hp.parameters.recenterConstant * δ ((F.tower.history n).toHistory.time i.succ)
      ≤ Hp.parameters.recenterConstant * (1 / (2 * Hp.parameters.recenterConstant)) :=
        mul_le_mul_of_nonneg_left hδ.le (by linarith)
    _ = 1 / 2 := by field_simp

end GC.LongTime.Ch11
