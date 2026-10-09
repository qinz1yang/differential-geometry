import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.A12FullConsumerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBandEstimatesNK

set_option autoImplicit false

/-!
# O-C12X-S17 (T9)：S17 Compat `CompatibleCapsSupply_C11E F q records`（后缀 `_C12X`）

设计：`docs/geometrization/chapter8/out/CH12X-S17-design.md`。陈述 = ch12
`CompatibleUpgradedCapRecords_S58`（`Ch11/EnhancedProfileDefsC11E:323` 逐字重述）。

**同一 physical cap 证书**（`s17_static_center_eq_C12X`）：同一 event 上任意两个 cutoff record
`R`（upgraded）与 `Q`（old）共享 event 的 tube `α`。`R.static b` 的 neck 中心 =
`R.neck α` 的 chart 在 `(m, ±1)`（`recenter_chart`）= `tube α (m, ±1)`（`R.tube_eq`）=
`Q.neck α` 的 chart 在同一坐标（`Q.tube_eq`）。

**scale 比较**（`s17_neck_scale_le_two_static_C12X`）：`Q.neck α` 是 `C^k`-`δ` neck（`k ≥ 6`），
`δ ≤ 1/8646` 时 `scalar_lower_NK` 给归一化 scalar `≥ 1/2`，于是
`Q.neck α .scale ≤ 2 · (R.static b).neck.scale`；`Q.scale_eq` 换成 `nominal⁻²`，`Ccmp = 2`
（与 `Dcap / p.modelRadius / p` 无关；linked window 与同族条件不用）。

**slice history**：`n := ⌈t⌉`、`i := Fin.castLE _ j`、`b' := b`；old record 经
`geometricCutoffRecordOfPrefix` 搬到 prefix（`neck / delta / tube_eq` 定义等式），time 子句 `rfl`。

唯一新输入：old record 的 tube `δ` 小（`q.delta` 在 event 时刻 `≤ 1/8646`；推论版：hext 已有的
`AntitoneOn q.delta (Ici 0)` + `q.delta 0 ≤ 1/8646`）。consumer：`a12Enhanced_of_chain_C11P2` /
`a12EnhancedFull_of_chain_C12X` 的 `hext` 中 S17 合取项换成 `q.delta 0 ≤ 1/8646`。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter TopologicalSpace
open scoped Topology NNReal ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-! ## 同一 physical cap -/

section SameCap

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p q : CutoffParameters}

/-- boundary 的符号坐标 `±1` 在 tube domain 的 `[-2, 2]` 里。 -/
theorem s17_sign_mem_C12X (c : Bool) : (if c then (1 : ℝ) else -1) ∈ Icc (-2 : ℝ) 2 := by
  cases c <;> norm_num

/-- **同一 physical cap**：record `R` 的 static cap 中心落在同一 event 上另一 record `Q` 的
tube neck `Q.neck α` 上，坐标 `(m, ±1)`（`m` = static neck 的 sphere mark，`±` = boundary 侧）。 -/
theorem s17_static_center_eq_C12X (R : GeometricCutoffRecord H i p)
    (Q : GeometricCutoffRecord H i q) (b : (H.event i).RetainedBoundaryIndex) :
    (R.static b).neck.center = (Q.neck b.1.1).chart
      ⟨((R.static b).neck.sphereMark, if b.1.2 then (1 : ℝ) else -1),
        Q.tube_in_buffer b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)⟩ := by
  have hR := R.tube_eq b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)
    (R.tube_in_buffer _ _)
  have hQ := Q.tube_eq b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)
    (Q.tube_in_buffer _ _)
  calc (R.static b).neck.center
      = (R.static b).neck.chart ⟨((R.static b).neck.sphereMark, 0), _⟩ :=
        (R.static b).neck.marked.symm
    _ = (R.neck b.1.1).chart ⟨((R.static b).neck.sphereMark,
          (if b.1.2 then (1 : ℝ) else -1) * (1 + 0)), _⟩ :=
        R.recenter_chart b _ (R.recenter_in_buffer b _)
    _ = (R.neck b.1.1).chart ⟨((R.static b).neck.sphereMark, if b.1.2 then (1 : ℝ) else -1),
          R.tube_in_buffer b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)⟩ :=
        congrArg _ (Subtype.ext (by simp))
    _ = _ := Subtype.ext (hR.symm.trans hQ)

/-- **scale 比较**：`Q` 的 tube `δ ≤ 1/8646` 时 `Q.neck α .scale ≤ 2 · (R.static b).neck.scale`。 -/
theorem s17_neck_scale_le_two_static_C12X (R : GeometricCutoffRecord H i p)
    (Q : GeometricCutoffRecord H i q) (b : (H.event i).RetainedBoundaryIndex)
    (hδ : Q.delta b.1.1 ≤ 1 / 8646) :
    (Q.neck b.1.1).scale ≤ 2 * (R.static b).neck.scale := by
  have hk : 2 ≤ Q.order b.1.1 :=
    le_trans (by omega) ((le_max_left _ _).trans (Q.order_lower b.1.1))
  have hδpos := Q.delta_pos b.1.1
  have hinv : 1 ≤ (Q.delta b.1.1)⁻¹ := (one_le_inv₀ hδpos).2 (by linarith)
  have hx : (⟨((R.static b).neck.sphereMark, if b.1.2 then (1 : ℝ) else -1),
      Q.tube_in_buffer b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)⟩ :
        neckBuffer (Q.delta b.1.1)) ∈ neckClosedTest (Q.delta b.1.1) := by
    change -(Q.delta b.1.1)⁻¹ ≤ (if b.1.2 then (1 : ℝ) else -1) ∧
      (if b.1.2 then (1 : ℝ) else -1) ≤ (Q.delta b.1.1)⁻¹
    cases b.1.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith
  have hlow := (Q.neck b.1.1).scalar_lower_NK hk hδ hx
  have hchart := (Q.neck b.1.1).metricScalarAt_chart_NK
    ⟨((R.static b).neck.sphereMark, if b.1.2 then (1 : ℝ) else -1),
      Q.tube_in_buffer b.1.1 ((R.static b).neck.sphereMark, ⟨_, s17_sign_mem_C12X b.1.2⟩)⟩
  rw [metricScalarAt_scaleMetric, ← s17_static_center_eq_C12X R Q b,
    ← (R.static b).neck.scale_scalar] at hchart
  have hpos := (Q.neck b.1.1).scale_pos
  have hS : (R.static b).neck.scale =
      (Q.neck b.1.1).scale * ((Q.neck b.1.1).scale⁻¹ * (R.static b).neck.scale) := by
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [hchart] at hS
  nlinarith

end SameCap

/-! ## S17 supply -/

/-- **S17**（event-时刻 δ 形）：`q.delta` 在每个 event 时刻 `≤ 1/8646` ⇒ Compat，`Ccmp = 2`。 -/
theorem compatibleCapsSupply_of_eventDelta_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (hδ : ∀ n (i : Fin (F.tower.history n).eventCount),
      q.delta ((F.tower.history n).time i.succ) ≤ 1 / 8646) :
    CompatibleCapsSupply_C11E F q records := by
  refine ⟨2, two_pos, fun s p j R b _ _ _ _ _ => ?_⟩
  let k := sliceStageR_C11E F s
  let i : Fin (F.tower.history (sliceIndexR_C11E F s)).eventCount :=
    Fin.castLE (Nat.le_of_lt_succ k.isLt) j
  refine ⟨sliceIndexR_C11E F s, i, b, rfl, ?_⟩
  have hQ := s17_neck_scale_le_two_static_C12X R
    ((F.tower.history (sliceIndexR_C11E F s)).geometricCutoffRecordOfPrefix k (i := j)
      (records _ i)) b (((records _ i).delta_le b.1.1).trans (hδ _ i))
  exact ((records _ i).scale_eq b.1.1).symm.trans_le hQ

/-- **S17**（参数形）：hext 已有的 `AntitoneOn q.delta (Ici 0)` + `q.delta 0 ≤ 1/8646` ⇒ Compat。 -/
theorem compatibleCapsSupply_of_astra_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hδ0 : q.delta 0 ≤ 1 / 8646) :
    CompatibleCapsSupply_C11E F q records :=
  compatibleCapsSupply_of_eventDelta_C12X records fun n i =>
    (hδanti (Set.mem_Ici.2 le_rfl) ((F.tower.history n).toHistory.time_nonneg i.succ)
      ((F.tower.history n).toHistory.time_nonneg i.succ)).trans hδ0

/-! ## consumer：hext 的 S17 合取项换成 `q.delta 0 ≤ 1/8646` -/

/-- consumer（逐字对 hext 合取项）：S17 producer 的输出正是 hext 第 19 项的类型。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (hδanti : AntitoneOn q.delta (Ici 0)) (hδ0 : q.delta 0 ≤ 1 / 8646) :
    CompatibleCapsSupply_C11E F q records :=
  compatibleCapsSupply_of_astra_C12X records hδanti hδ0

/-- **A12′ 从链（S17 已供给）**：`a12Enhanced_of_chain_C11P2` 的 `hext`，S17 合取项
`CompatibleCapsSupply_C11E F q records` 换成参数界 `q.delta 0 ≤ 1/8646`（其余 19 项逐字）。 -/
theorem a12Enhanced_of_chain_S17_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε = C.epsilon ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        q.delta 0 ≤ 1 / 8646 ∧ FrontierCollarSupply_C11E F q) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, hδ0, h20⟩ := hext
  exact a12Enhanced_of_chain_C11P2 hP3 hprof ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    compatibleCapsSupply_of_astra_C12X records h7 hδ0, h20⟩

/-- **A12′ v2 从链（S17 已供给）**：`a12EnhancedFull_of_chain_C12X` 的 `hext`，S17 合取项换成
`q.delta 0 ≤ 1/8646`（RFC-a 末项为全称形，其余逐字）。 -/
theorem a12EnhancedFull_of_chain_S17_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε = C.epsilon ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        q.delta 0 ≤ 1 / 8646 ∧ FrontierCollarSupplyFull_C11F F q) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, hδ0, h20⟩ := hext
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    compatibleCapsSupply_of_astra_C12X records h7 hδ0, h20⟩

end GC.LongTime.Ch11
