import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S

set_option autoImplicit false

/-!
# O-CH11-PROF (G2)：A12′ 的陈述、A12′ ⇒ A12 的投影、A13 binder 的提取

* `A12EnhancedConclusion_C11E P g`：A12 的结论把 `hasAnalyticAdmissibility F δ` 换成
  `hasEnhancedAdmissibility_C11E F δ`；`A12EnhancedStatement_C11E` 是它的全称形（= A12′）。
  本车道规则不许 `sorry`，所以 A12′ 在这里是 `Prop`；INT 在用户 GO 后把它作为 admission
  `exists_surgery_with_decaying_accuracy_enhanced`（`theorem … := by sorry`）落入 tracked 文件，
  取代 A12 在 ledger 里的位置（design §2）。
* `exists_surgery_with_decaying_accuracy_of_enhanced_C11E`：**A12′ ⇒ A12**，0 sorry（`type_of%` 对齐）。
* `EnhancedSurgeryProfile_C11E.hrc`：ch12 的 `hrc` binder 由 decay 推出（不是字段）。
* `a13ProfileBinders_of_enhanced_C11E`：ch12 A13 wiring（`A13Wiring_S32.lean:47–57`）的
  profile 级 binder `hadm Hp hP1 Ctime hP2 hP3 hP4 hP6` 逐个由 enhanced admissibility 给出；
  `ch12SupplyBinders_of_enhanced_C11E`：hone / K-core 链要的 hStrong v2、Compat、hprof、`hscale`、`hrc`。
* `A13EnhancedStatement_C11E`：tracked A13 `late_derivative_tests_of_flow` 改吃 enhanced 后的陈述
  （M2-pre 起 binder 是 v2 `hasEnhancedAdmissibilityFull_C11F`，`Ch11/EnhancedProfileFullC11F.lean`）；
  `example`：S32 形 wiring + ch12 内部残余（hG2、hMicro）⇒ 它。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## A12′ -/

/-- **A12′ 的结论**（`P g` 固定）：与 A12 逐字相同，只把最后一项换成 enhanced admissibility。 -/
def A12EnhancedConclusion_C11E (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
    AntitoneOn δ (Ici 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
    hasEnhancedAdmissibility_C11E F δ

/-- **A12′**（全称陈述）：`exists_surgery_with_decaying_accuracy_enhanced` 的类型。 -/
def A12EnhancedStatement_C11E.{v} : Prop :=
  ∀ (P : OrientedThreeStage.{v}) (g : P.Metric), A12EnhancedConclusion_C11E P g

/-- **投影 A12′ ⇒ A12**（逐 `P g`；结论与 A12 逐字相同）。 -/
theorem exists_surgery_with_decaying_accuracy_of_enhanced_C11E {P : OrientedThreeStage.{u}}
    {g : P.Metric} (h : A12EnhancedConclusion_C11E P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  let ⟨δ, F, ha, hd, hE⟩ := h
  ⟨δ, F, ha, hd, hasAnalyticAdmissibility_of_enhanced_C11E hE⟩

/-- 全称版：A12′ ⇒ A12 的全称陈述。 -/
theorem a12_of_a12Enhanced_C11E (h : A12EnhancedStatement_C11E.{u})
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_enhanced_C11E (h P g)

/-- 逐字对齐：投影的类型就是 A12（显式保留原 A12 的陈述）。 -/
example (h : A12EnhancedStatement_C11E.{u}) (P : OrientedThreeStage.{u}) (g : P.Metric) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  a12_of_a12Enhanced_C11E h P g

/-- consumer（sorry-free）：A12′ ⇒ 晚期 decay 的共同 neck accuracy。 -/
theorem commonNeckAccuracy_of_enhanced_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (h : A12EnhancedConclusion_C11E P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-! ## 从 enhanced profile 提取 ch12 的 binder -/

section Binders

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- `hrc`（ch12 S89 / S97 / S118 的 binder 逐字）：不是字段，由 decay 推出。 -/
theorem EnhancedSurgeryProfile_C11E.hrc (E : EnhancedSurgeryProfile_C11E F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ Trc : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      Trc ≤ (F.tower.history n).toHistory.time i.succ →
      E.toAnalyticSurgeryProfile.parameters.recenterConstant *
        E.toAnalyticSurgeryProfile.parameters.delta
          ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2 :=
  hrc_of_decay_C11S E.toAnalyticSurgeryProfile hdec

/-- **A13 wiring 的 profile 级 binder 包**（ch12 `late_derivative_tests_of_flow_of_supplies_S32`
的 `hadm`、`Hp`、`hP1`、`Ctime`、`hP2`、`hP3`、`hP4`、`hP6`，同一个 `Hp`）。 -/
theorem a13ProfileBinders_of_enhanced_C11E (h : hasEnhancedAdmissibility_C11E F δ) :
    hasAnalyticAdmissibility F δ ∧
      ∃ Hp : AnalyticSurgeryProfile F δ, P1_C11E Hp ∧
        ∃ Ctime : ℝ≥0, P2_C11E Hp Ctime ∧ P3_C11E Hp ∧ P4_C11E Hp ∧ P6_C11E Hp := by
  obtain ⟨E⟩ := h
  exact ⟨⟨E.toAnalyticSurgeryProfile⟩, E.toAnalyticSurgeryProfile, E.linked_windows, E.Ctime,
    E.time_derivative, E.collar_window, E.epsilon_cone, E.larger_ball_canonical⟩

/-- **ch12 其余 ch11 供给的 binder 包**（同一个 `Hp`）：P5Linked、hStrong v2、Compat、
hprof（常数 = `εProf_C11E`）、RFC-a、`hscale`（S119 的 exact `/2` 形）、`hrc`。 -/
theorem ch12SupplyBinders_of_enhanced_C11E (h : hasEnhancedAdmissibility_C11E F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ Hp : AnalyticSurgeryProfile F δ,
      P5Linked_C11E Hp ∧ StrongCanonicalSupply_C11E Hp ∧ CompatibleUpgradedCapRecords_C11E Hp ∧
      hprof_C11E Hp εProf_C11E.{u} ∧ RFCa_C11E Hp ∧
      (∀ n (i : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z)) ∧
      ∃ Trc : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
        Trc ≤ (F.tower.history n).toHistory.time i.succ →
        Hp.parameters.recenterConstant *
          Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2 := by
  obtain ⟨E⟩ := h
  exact ⟨E.toAnalyticSurgeryProfile, E.late_linked_records, E.strong_canonical,
    E.compatible_cap_records, E.model_constraints, E.frontier_collar, E.hscale, E.hrc hdec⟩

end Binders

/-! ## A13 改吃 A12′ -/

/-- tracked A13（`LT/LateCutGeometry.lean:158`）改签名后的陈述：`hadm` 换成 enhanced admissibility
（M2-pre：v2 `hasEnhancedAdmissibilityFull_C11F`）。 -/
def A13EnhancedStatement_C11E.{v} : Prop :=
  ∀ {P : OrientedThreeStage.{v}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ),
    lateDerivativeOrder ≤ K → ∀ (δ : ℝ → ℝ), hasEnhancedAdmissibilityFull_C11F F δ →
    (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) →
    ∀ (slices : ℕ → RegularSlice F.observation),
      (∀ j : ℕ, (j : ℝ) < (slices j).time) →
      (∀ j : ℕ, Nonempty (slices j).stage.Carrier) →
      ∀ L : LateCutFamily F K slices, L.hasEventualDerivativeBounds

/-- 接法（Prop 形）：ch12 S32 形 wiring（binder `hadm hdec Hp hP1 Ctime hP2 hP3 hP4 hP6` + ch12 内部残余
`Rest Hp Ctime` = hG2 ∧ hMicro）加上"残余对每个 enhanced profile 成立"⇒ 改签名后的 A13。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (δ : ℝ → ℝ) (slices : ℕ → RegularSlice F.observation) (L : LateCutFamily F K slices)
    (Rest : AnalyticSurgeryProfile F δ → ℝ≥0 → Prop)
    (hS32 : hasAnalyticAdmissibility F δ →
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) →
      ∀ Hp : AnalyticSurgeryProfile F δ, P1_C11E Hp → ∀ Ctime : ℝ≥0, P2_C11E Hp Ctime →
        P3_C11E Hp → P4_C11E Hp → P6_C11E Hp → Rest Hp Ctime → L.hasEventualDerivativeBounds)
    (hrest : ∀ E : EnhancedSurgeryProfile_C11E F δ, Rest E.toAnalyticSurgeryProfile E.Ctime)
    (hadm : hasEnhancedAdmissibility_C11E F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    L.hasEventualDerivativeBounds := by
  obtain ⟨E⟩ := hadm
  exact hS32 ⟨E.toAnalyticSurgeryProfile⟩ hdec E.toAnalyticSurgeryProfile E.linked_windows E.Ctime
    E.time_derivative E.collar_window E.epsilon_cone E.larger_ball_canonical (hrest E)

/- The legacy admission-consuming example was retired; proved enhanced consumers live downstream. -/

end GC.LongTime.Ch11
