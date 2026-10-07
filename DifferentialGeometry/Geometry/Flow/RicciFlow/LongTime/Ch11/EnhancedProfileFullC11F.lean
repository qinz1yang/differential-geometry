import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E

set_option autoImplicit false

/-!
# O-CH11-MERGE (M2)：enhanced profile v2 = ch12 终端 binder 的全部 ch11 供给（后缀 `_C11F`）

`Ch11/EnhancedProfileDefsC11E.lean`（PROF G1，已交，**不改**）之上的 rev 文件；lead 02:1x 裁定 U1–U3：

* **U1 hRFCa**：PROF 的 `FrontierCollarSupply_C11E`（`∃ εFr Tf`、只晚期 slice、accuracy ≤ `εFr`）弱于 ch12
  终端 `A13_of_supplies_S153` / `A09_of_supplies_S153` 的 `hRFCa` binder（ch12 S148：全 slice、
  accuracy ≤ `3/4`、无 `∃`）。这里按终端文本逐字新写 `FrontierCollarSupplyFull_C11F`
  （`sliceHistoryR_O3 → sliceHistoryR_C11E`、`linkedCanonicalWindow_O2 → linkedCanonicalWindow_C11E`、
  `Hp.parameters → q`），profile 加字段
  `frontier_collar_full`；旧字段由它推出（`frontierCollarSupply_of_full_C11F`），所以
  `EnhancedSurgeryProfileFull_C11F` 的内容恰是"旧字段集，RFC-a 换成终端形"
  （`hasEnhancedAdmissibilityFull_iff_C11F`）。
* **U2 hStrong**：字段保留 v2（`StrongCanonicalSupplyV2_C11E`，`[FROZEN v2] CH12-O31`）；终端 binder 是 v1，
  `strongCanonicalSupplyV1_of_v2_C11F` 丢掉 `a E` 与窗口拉回子句（仿 ch12 `hStrong_v1_of_v2_O31`）。
* **U3 heps / hCapWin**：不加字段。`heps` 由 P4（`ε ≤ εKL70`）算术推出（`heps_of_coneEpsilon_C11F`）；`hCapWin`
  （RFC-c，`[FROZEN] CH12-S133`）对任意 profile 成立：binder 自带 linked window 前提，其第三合取项给出
  `‖x‖ ≤ transitionEnd < Dcap`（`capWindowClause_C11F`）。

A12′ 的 Full 形 `A12EnhancedFullConclusion_C11F`（tracked admission 改指它）与投影 Full ⇒ `_C11E`。
本文件只 import PROF G1，**不** import `LateCutGeometry` 或任何 `Ch12/*`（ch12 merge 前编过；merge 后的
`Iff.rfl` 互换在 `WR/EnhancedBridgeC11M.lean`）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## U1：RFC-a 终端形（ch12 `A13Final_S153.lean` 的 `hRFCa` binder，逐字） -/

/-- **S19′**（RFC-a 终端形，data 级；`Hp.parameters → q`）：每个 slice history 上参数与 `q` 同族、
半径 `> transitionEnd + 3`、accuracy `≤ 3/4`、阶 `≥ 4`、有 linked windows 的 record，event 旧输出的 frontier
落在某个 retained boundary 的 retained collar（`z' ≤ 1`）里。 -/
def FrontierCollarSupplyFull_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) : Prop :=
  ∀ (s : RegularSlice F.observation) (pp : CutoffParameters),
    pp.delta = q.delta → pp.neckRadius = q.neckRadius →
    pp.fixed = q.fixed → pp.recenterConstant = q.recenterConstant →
    StandardCap.transitionEnd + 3 < pp.modelRadius → pp.modelAccuracy ≤ 3 / 4 →
    4 ≤ pp.modelOrder →
    ∀ (i : Fin (sliceHistoryR_C11E F s).eventCount)
      (R : GeometricCutoffRecord (sliceHistoryR_C11E F s).toHistory i pp),
      (∀ b, linkedCanonicalWindow_C11E (R.static b)) →
      ∀ y ∈ frontier (range ((sliceHistoryR_C11E F s).toHistory.event i).oldOutput),
        ∃ (b : ((sliceHistoryR_C11E F s).toHistory.event i).RetainedBoundaryIndex)
          (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
            (R.static b).inclusion ((R.static b).witness.retained c) = y

/-- 终端形 ⇒ PROF 的 S19（`εFr := 3/4`、`Tf := 0`）。 -/
theorem frontierCollarSupply_of_full_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (h : FrontierCollarSupplyFull_C11F F q) : FrontierCollarSupply_C11E F q :=
  ⟨3 / 4, 0, by norm_num, fun s _ pp j R hd hn hf hr hacc hord hrad hlink =>
    h s pp hd hn hf hr hrad hacc hord j R hlink⟩

/-! ## U2：hStrong 终端形 v1（ch12 `A13Final_S153.lean` 的 `hStrong` binder，逐字） -/

/-- **S16v1**（hStrong v1 体；`Hp.parameters.neckRadius → ρ`、`Hp.epsilon / C1 / C2 → ε C1 C2`）。 -/
def StrongCanonicalSupplyV1_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ x : s.stage.Carrier,
    ∀ hR : (ρ s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
    ∃ W : SpatialCanonicalWitness s.metric ε C1 C2 x,
      W.capTubeHasNeckChart ε ∧
      ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
        ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
          (S : SolutionOn (I := ThreeModel) (M := U)
            (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
              (sub_le_self _ (inv_nonneg.mpr
                (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
          IsSolutionOn S ∧ S.base.metric s.time = s.metric.restrictOpen U ∧
          Nonempty (StrongNeck S ε ⟨x, hxU⟩ s.time)

/-- **v2 ⇒ v1**：丢掉 backward window 的起点 `a`、trace `E`、`a` 的值与窗口拉回子句。 -/
theorem strongCanonicalSupplyV1_of_v2_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 : ℝ}
    (h : StrongCanonicalSupplyV2_C11E F ρ ε C1 C2) : StrongCanonicalSupplyV1_C11F F ρ ε C1 C2 := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hW, hneck⟩ := hT s hs x hR
  refine ⟨W, hW, fun nk hnk => ?_⟩
  obtain ⟨U, hxU, -, -, S, -, hS, -, hbase, hstrong⟩ := hneck nk hnk
  exact ⟨U, hxU, S, hS, hbase, hstrong⟩

/-! ## U3：heps 与 hCapWin 由已有字段 / 无条件推出 -/

/-- **heps**（ch12 终端 binder 逐字）由 P4 体 `ε ≤ εKL70_C11E` 推出。 -/
theorem heps_of_coneEpsilon_C11F {ε : ℝ} (h : ConeEpsilonSupply_C11E ε) :
    13000 * (13000 * ε) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64) := by
  have h' : ε ≤ min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) /
      (13000 * 13000) := h
  rw [le_div_iff₀ (by norm_num)] at h'
  linarith

section Profile

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **RFC-a 终端形**（profile 级，= ch12 `hRFCa` binder）。 -/
def RFCaFull_C11F (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  FrontierCollarSupplyFull_C11F F Hp.parameters

/-- **hStrong v1**（profile 级，= ch12 `hStrong` binder）。 -/
def StrongCanonicalV1_C11F (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  StrongCanonicalSupplyV1_C11F F Hp.parameters.neckRadius Hp.epsilon Hp.C1 Hp.C2

/-- **RFC-c / hCapWin**（profile 级，= ch12 `hCapWin` binder 逐字，
`sliceHistoryR_O3 → sliceHistoryR_C11E`、`linkedCanonicalWindow_O2 → linkedCanonicalWindow_C11E`）。 -/
def CapWindowClause_C11F (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
    ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
    ∀ (pp : CutoffParameters)
      (records : ∀ i : Fin (sliceHistoryR_C11E F s).eventCount,
        T₀ - θ ≤ (sliceHistoryR_C11E F s).time i.succ →
        GeometricCutoffRecord (sliceHistoryR_C11E F s).toHistory i pp),
      pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
      pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
      32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
      pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
      (∀ i hi b, linkedCanonicalWindow_C11E ((records i hi).static b)) →
    ∀ (j : Fin (sliceHistoryR_C11E F s).eventCount)
      (hj : T₀ - θ ≤ (sliceHistoryR_C11E F s).time j.succ)
      (b : ((sliceHistoryR_C11E F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
        ((records j hj).static b).window x =
          ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z)

/-- **hCapWin 无条件成立**（`Tc := 0`、`εc := 1`）：linked window 的第三合取项给 cap 点一个
`‖x‖ ≤ transitionEnd` 的窗口原像，而 `transitionEnd + 3 < Dcap`。 -/
theorem capWindowClause_C11F (Hp : AnalyticSurgeryProfile F δ) : CapWindowClause_C11F Hp := by
  intro θ Dcap hD
  refine ⟨0, 1, one_pos, ?_⟩
  intro s _ T₀ _ _ pp records _ _ _ _ _ _ _ hlink j hj b z
  obtain ⟨-, -, -, -, -, -, -, h3, -, -⟩ := hlink j hj b
  obtain ⟨x, hx, hwin⟩ := h3 z
  exact ⟨x, by linarith, hwin⟩

/-- 新字段的合取（v2 版：RFC-a 取终端形；`Ctime` 给定）。 -/
def EnhancedFieldsFull_C11F (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) : Prop :=
  P1_C11E Hp ∧ P2_C11E Hp Ctime ∧ P3_C11E Hp ∧ P4_C11E Hp ∧ P5Linked_C11E Hp ∧ P6_C11E Hp ∧
    StrongCanonicalSupply_C11E Hp ∧ CompatibleUpgradedCapRecords_C11E Hp ∧
    hprof_C11E Hp εProf_C11E.{u} ∧ RFCaFull_C11F Hp

end Profile

/-! ## enhanced profile v2 -/

/-- **enhanced profile v2**（A12′ 的 profile，U1）：PROF 的 enhanced profile 加 RFC-a 终端形字段。
旧字段 `frontier_collar` 由新字段推出（`ofFieldsFull`），故内容 = `EnhancedFieldsFull_C11F`。 -/
structure EnhancedSurgeryProfileFull_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) extends EnhancedSurgeryProfile_C11E F δ where
  frontier_collar_full : RFCaFull_C11F toAnalyticSurgeryProfile

/-- A12′（v2）的 admissibility。 -/
def hasEnhancedAdmissibilityFull_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) : Prop :=
  Nonempty (EnhancedSurgeryProfileFull_C11F F δ)

section API

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **投影** v2 ⇒ PROF 的 enhanced admissibility。 -/
theorem hasEnhancedAdmissibility_of_full_C11F (h : hasEnhancedAdmissibilityFull_C11F F δ) :
    hasEnhancedAdmissibility_C11E F δ :=
  let ⟨E⟩ := h
  ⟨E.toEnhancedSurgeryProfile_C11E⟩

/-- **投影** v2 ⇒ 原 admissibility（A09 / G_final 的 `hadm`）。 -/
theorem hasAnalyticAdmissibility_of_full_C11F (h : hasEnhancedAdmissibilityFull_C11F F δ) :
    hasAnalyticAdmissibility F δ :=
  hasAnalyticAdmissibility_of_enhanced_C11E (hasEnhancedAdmissibility_of_full_C11F h)

/-- 由原 profile + `Ctime` + v2 字段构造（旧 RFC-a 字段由终端形推出；条件 inhabitant）。 -/
def EnhancedSurgeryProfileFull_C11F.ofFieldsFull (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0)
    (h : EnhancedFieldsFull_C11F Hp Ctime) : EnhancedSurgeryProfileFull_C11F F δ :=
  { toEnhancedSurgeryProfile_C11E := EnhancedSurgeryProfile_C11E.ofFields Hp Ctime
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
        frontierCollarSupply_of_full_C11F h.2.2.2.2.2.2.2.2.2⟩
    frontier_collar_full := h.2.2.2.2.2.2.2.2.2 }

/-- v2 profile 的字段合取。 -/
theorem EnhancedSurgeryProfileFull_C11F.fieldsFull (E : EnhancedSurgeryProfileFull_C11F F δ) :
    EnhancedFieldsFull_C11F E.toAnalyticSurgeryProfile E.Ctime :=
  ⟨E.linked_windows, E.time_derivative, E.collar_window, E.epsilon_cone, E.late_linked_records,
    E.larger_ball_canonical, E.strong_canonical, E.compatible_cap_records, E.model_constraints,
    E.frontier_collar_full⟩

/-- **相对非空真**：v2 admissibility 恰是"同一个 profile 上 v2 字段成立"（旧 RFC-a 字段不加内容）。 -/
theorem hasEnhancedAdmissibilityFull_iff_C11F :
    hasEnhancedAdmissibilityFull_C11F F δ ↔
      ∃ (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0), EnhancedFieldsFull_C11F Hp Ctime :=
  ⟨fun ⟨E⟩ => ⟨E.toAnalyticSurgeryProfile, E.Ctime, E.fieldsFull⟩,
    fun ⟨Hp, Ctime, h⟩ => ⟨EnhancedSurgeryProfileFull_C11F.ofFieldsFull Hp Ctime h⟩⟩

/-- consumer（U2）：v2 profile 给终端的 hStrong v1。 -/
theorem EnhancedSurgeryProfileFull_C11F.strongV1 (E : EnhancedSurgeryProfileFull_C11F F δ) :
    StrongCanonicalV1_C11F E.toAnalyticSurgeryProfile :=
  strongCanonicalSupplyV1_of_v2_C11F E.strong_canonical

/-- consumer（U3）：v2 profile 给终端的 heps。 -/
theorem EnhancedSurgeryProfileFull_C11F.heps (E : EnhancedSurgeryProfileFull_C11F F δ) :
    13000 * (13000 * E.toAnalyticSurgeryProfile.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64) :=
  heps_of_coneEpsilon_C11F E.epsilon_cone

end API

/-! ## A12′（v2） -/

/-- **A12′ v2 的结论**（`P g` 固定）：A12 的结论把 `hasAnalyticAdmissibility F δ` 换成 v2 admissibility。 -/
def A12EnhancedFullConclusion_C11F (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
    AntitoneOn δ (Ici 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
    hasEnhancedAdmissibilityFull_C11F F δ

/-- **A12′ v2**（全称陈述）：tracked admission `exists_surgery_with_decaying_accuracy_enhanced` 的新类型。 -/
def A12EnhancedFullStatement_C11F.{v} : Prop :=
  ∀ (P : OrientedThreeStage.{v}) (g : P.Metric), A12EnhancedFullConclusion_C11F P g

/-- **投影** A12′ v2 ⇒ A12′（PROF 形，= `A12EnhancedConclusion_C11E P g` 的展开）。 -/
theorem a12EnhancedConclusion_of_full_C11F {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasEnhancedAdmissibility_C11E F δ :=
  let ⟨δ, F, ha, hd, hE⟩ := h
  ⟨δ, F, ha, hd, hasEnhancedAdmissibility_of_full_C11F hE⟩

/-- consumer：A12′ v2 ⇒ 晚期 decay 的共同 neck accuracy（sorry-free）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

end GC.LongTime.Ch11
