import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A

set_option autoImplicit false

/-!
# S-CH11-ENHSUP (G2)：enhanced 字段（`_C11E`）← 已落地 astra 模块 / narrow tuple 的对齐（后缀 `_C11P2`）

producer 盘点表见 `docs/geometrization/chapter8/CH11-ENHSUP-20261007.md`。这里只写**现在就能对齐**的部分
（0 sorry，无新具名 Prop）：

* S13 / P4 ⇐ `ClosedBirthConstants.epsilon_cone`（`coneEpsilonSupply_of_closedBirth_C11P2`）；
* S12 / P3、S18 / hprof ⇐ narrow tuple 的 `q.fixed / modelRadius / modelOrder / modelAccuracy
  = pBase.·`
  （`collarWindowSupply_of_static_C11P2`、`modelConstraintsSupply_of_static_C11P2`、
  `w1_params_of_preparedSpatialChain_C11P2`：W1 十合取项 + 这三个字段落在同一个 `(F, q, records)` 上）；
* S11 / P2 ⇐ astra `PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold`
  （`SH/PreparedSpatialDiagonalDerivative:74`，**未落地**：verbatim overlay 4 error）的结论形：
  `timeDerivativeSupply_of_diagonal_C11P2` 把它的 `stageMetric / activeStage` 形换成 P2 的
  `incoming.flow.scalar / finalSlab` 形（binder 逐字取自 astra 陈述，ASM G2 同口径）；
* S16 hStrong v2 的结构部分：`RegularOpenBackwardTrace_C11E H first U` ⇔ `U ≤ H.backwardSurvivorDomain …`
  （`regularOpenBackwardTrace_iff_le_survivorDomain_C11P2`）——`_C11E` 的 trace 结构在树内
  `HistorySurvivorDomain` 里**逐字存在**，不是新内容；
* S15 / P6：`LargerBallCanonicalLateSupply_C11E ↔ P6LateSupply_P6A`（`Iff.rfl`）；
* consumer：`∃ S` + 公共参数 P3 / hprof + "扩充 outer tuple" 的剩余字段 ⇒ `A12EnhancedConclusion_C11E`
  （`a12Enhanced_of_chain_C11P2`，剩余字段清单 = 它的 `hext` 的最后 8 个合取项）。

不在这里的字段（P1 的 link 子句、P5Linked、S17 Compat、S19 RFC-a、S16 的 `StrongNeck` 部分、S15 的 `A > 1`）
没有 astra 同义陈述，见 docs 表的 (c)/(d) 行。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter TopologicalSpace
open scoped Topology NNReal ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-! ## S13 / P4 ⇐ `ClosedBirthConstants.epsilon_cone` -/

/-- **S13**（P4）⇐ astra `ClosedBirthConstants.epsilon_cone : epsilon ≤ coneAccuracy`（DIGEST C3）；
`w1_of_preparedSpatialChain_C11A` 里的 `ε` 就是 `C.epsilon`。 -/
theorem coneEpsilonSupply_of_closedBirth_C11P2 (C : GC.GeneralFlow.ClosedBirthConstants) :
    ConeEpsilonSupply_C11E C.epsilon :=
  coneEpsilonSupply_of_le_coneAccuracy_C11E C.epsilon_cone

/-! ## S12 / P3、S18 / hprof ⇐ narrow tuple 的 `q.· = pBase.·` -/

/-- **S12**（P3）沿 `q.fixed = p.fixed`、`q.modelRadius = p.modelRadius` 传递。 -/
theorem collarWindowSupply_of_static_C11P2 {q p : CutoffParameters}
    (hfixed : q.fixed = p.fixed) (hrad : q.modelRadius = p.modelRadius)
    (h : CollarWindowSupply_C11E.{u} p) : CollarWindowSupply_C11E.{u} q := by
  have key : ∀ (A A' : ℝ) (hA : 0 < A) (hA' : 0 < A'), A = A' →
      collarAdmitsAllOrders_C11E.{u} A hA → collarAdmitsAllOrders_C11E.{u} A' hA' := by
    intro A A' _ _ e h
    subst e
    exact h
  refine ⟨key _ _ _ _ (congrArg StaticCapScaffold.collarLength hfixed.symm) h.1, ?_⟩
  rw [hrad]
  exact h.2

/-- **S18**（hprof）沿 `q.modelAccuracy / modelOrder / modelRadius = p.·` 传递。 -/
theorem modelConstraintsSupply_of_static_C11P2 {q p : CutoffParameters} {ε₀ : ℝ}
    (hacc : q.modelAccuracy = p.modelAccuracy) (hord : q.modelOrder = p.modelOrder)
    (hrad : q.modelRadius = p.modelRadius) (h : ModelConstraintsSupply_C11E p ε₀) :
    ModelConstraintsSupply_C11E q ε₀ := by
  unfold ModelConstraintsSupply_C11E at h ⊢
  rw [hacc, hord, hrad]
  exact h

/-- **W1 + 参数级 enhanced 字段**：`S : PreparedSpatialChain pBase C P g` 且 `pBase` 满足 P3 / hprof
（参数选择，树内 `sampleEnhancedParameters_C11E` 是 inhabitant），则 narrow tuple 的同一个
`(F, q, κ, records)` 上，W1 的十个合取项（同 `w1_of_preparedSpatialChain_C11A`）与 P3、hprof、
`ε = C.epsilon` 的 P4 同时成立。 -/
theorem w1_params_of_preparedSpatialChain_C11P2 {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u}) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      F.tower = S.tower ∧ ε = C.epsilon ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t) ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      CollarWindowSupply_C11E.{u} q ∧ ModelConstraintsSupply_C11E q εProf_C11E.{u} ∧
      ConeEpsilonSupply_C11E ε := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin,
    hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  obtain ⟨hfixed, hrad, hord, hacc, -⟩ := hstatic
  refine ⟨F, q, κ, records, C.epsilon, max C.C1s C.Cbirth,
    max C.C2s (max C.Cbirth (C.Cgrad : ℝ)), hTower, rfl, ⟨hfixed, hrad, hord, hacc⟩, fun t ht => ?_,
    canonicalConstantsSupply_of_closedBirthConstants_C11A C, hκ, hκanti, hδanti, hρanti,
    hcan, hwin, hnc, hδlim, hrecent, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
    modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
    coneEpsilonSupply_of_closedBirth_C11P2 C⟩
  change q.delta t = ((S.observation (Nat.ceil t)).parameters).delta t
  exact (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).1

/-! ## S11 / P2 ⇐ astra `scalar_time_derivative_at_diagonal_threshold` 的结论形 -/

/-- **S11**（P2）⇐ astra `PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold`
（`SH/PreparedSpatialDiagonalDerivative:74`）的结论：`hdiag` 逐字取自它（`q.neckRadius → ρ`，
`C.Ctime → Ctime`，`F.tower.history n` 上的 active-stage 形）。P2 的形是 event slab 的
`incoming.flow.scalar` 与 final slab 的 `finalSlab.flow.scalar`；二者在 `stageMetric` 的定义里
是 `Fin.lastCases` 的两支（`stageMetric_castSucc_apply`、`stageMetric_last_of_lt`），本定理做这个换形。
`hdiag` 的 producer = astra 该定理（输入 outer tuple 的 `W / hshift / hoffset`），目前未落地。 -/
theorem timeDerivativeSupply_of_diagonal_C11P2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (Ctime : ℝ≥0)
    (hdiag : ∀ (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).time ((F.tower.history n).toHistory.activeStage v) < (v : ℝ) →
      (v : ℝ) < (F.tower.history n).toHistory.horizon →
      (ρ v ^ 2)⁻¹ < metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2) :
    TimeDerivativeSupply_C11E F ρ Ctime := by
  constructor
  · intro n j y t ht hR
    let H : ObservedHistory.{u} := (F.tower.history n).toHistory
    have ht' : t ∈ Ioo (H.time j.castSucc) (H.time j.succ) := ht
    have hlt : t < H.horizon := ht'.2.trans_le (H.time_le_horizon_at _)
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg _).trans ht'.1.le, hlt.le⟩
    have hact : H.activeStage v = j.castSucc :=
      (H.mem_stageDomain_iff v j.castSucc).mp
        (H.mem_stageDomain_of_mem_Ioo (by simpa only [H.stageEndTime_castSucc] using ht'))
    have key : ∀ k (_ : H.activeStage v = k) (z : (H.stage k).Carrier), H.time k < (v : ℝ) →
        (ρ v ^ 2)⁻¹ < metricScalarAt (H.stageMetric k v) z →
        |derivWithin (fun s => metricScalarAt (H.stageMetric k s) z) (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt (H.stageMetric k v) z ^ 2 := by
      intro k hk
      subst hk
      exact fun z h1 h2 => hdiag n v z h1 hlt h2
    have hmain := key j.castSucc hact y ht'.1
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hmain
    exact hmain hR
  · intro n h y t ht hR
    let H : ObservedHistory.{u} := (F.tower.history n).toHistory
    have ht' : t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon := ht
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg _).trans ht'.1.le, ht'.2.le⟩
    have hact : H.activeStage v = Fin.last H.eventCount :=
      (H.mem_stageDomain_iff v (Fin.last H.eventCount)).mp
        (H.mem_stageDomain_of_mem_Ioo (by simpa only [H.stageEndTime_last] using ht'))
    have key : ∀ k (_ : H.activeStage v = k) (z : (H.stage k).Carrier), H.time k < (v : ℝ) →
        (ρ v ^ 2)⁻¹ < metricScalarAt (H.stageMetric k v) z →
        |derivWithin (fun s => metricScalarAt (H.stageMetric k s) z) (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt (H.stageMetric k v) z ^ 2 := by
      intro k hk
      subst hk
      exact fun z h1 h2 => hdiag n v z h1 ht'.2 h2
    have h' : H.time (Fin.last H.eventCount) < H.horizon := h
    have hmain := key (Fin.last H.eventCount) hact y ht'.1
    simp only [ObservedHistory.stageMetric_last_of_lt (h := h')] at hmain
    exact hmain hR

/-! ## S16 hStrong v2 的 trace 结构 ⇔ 树内 `backwardSurvivorDomain` -/

/-- **S16 的结构部分**：`RegularOpenBackwardTrace_C11E H first U` 存在 ⇔ `U` 落在树内
`H.backwardSurvivorDomain first (last) _` 里。⇒：`survive` 就是 domain 的成员条件；⇐：local diffeo
由树内 `backwardSurvivorMap_isLocalDiffeomorph`（`HistorySurvivorDomain:127`）复合开集包含。
所以 hStrong v2 里的 `E` 不是新内容；新内容全在 `StrongNeck S ε ⟨x, hxU⟩ s.time`。 -/
theorem regularOpenBackwardTrace_iff_le_survivorDomain_C11P2 {H : ObservedHistory.{u}}
    {first : Fin (H.eventCount + 1)} {U : Opens (H.stage (Fin.last H.eventCount)).Carrier} :
    Nonempty (RegularOpenBackwardTrace_C11E H first U) ↔
      U ≤ H.backwardSurvivorDomain first (Fin.last H.eventCount) (Fin.le_last first) := by
  constructor
  · rintro ⟨E⟩ x hx
    exact E.survive x hx
  · intro hU
    refine ⟨⟨fun x hx => hU hx, fun j hj hl => ?_⟩⟩
    have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Opens.inclusion hU) := by
      apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
        (contMDiff_inclusion hU) _ rfl
      intro x
      rw [mfderiv_opens_incl]
      exact Function.injective_id
    exact DifferentialGeometry.isLocalDiffeomorph_comp
      (H.backwardSurvivorMap_isLocalDiffeomorph first (Fin.last H.eventCount)
        (Fin.le_last first) j hj hl) hinc

/-- consumer：`first = last` 时任意开集都在 domain 里（`regularOpenBackwardTrace_last_C11E` 的另一证法）。 -/
example (H : ObservedHistory.{u})
    (U : Opens (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (RegularOpenBackwardTrace_C11E H (Fin.last H.eventCount) U) :=
  regularOpenBackwardTrace_iff_le_survivorDomain_C11P2.2
    fun x _ => H.mem_backwardSurvivorDomain_self _ x

/-! ## S15 / P6：statement 对齐 -/

/-- `P6_C11E` 的数据级体与 P6A 的 `P6LateSupply_P6A` 逐字同（design §8 预期的 `Iff.rfl`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (ε C1 C2 : ℝ) :
    LargerBallCanonicalLateSupply_C11E F ε C1 C2 ↔ P6LateSupply_P6A F ε C1 C2 :=
  Iff.rfl

/-! ## consumer：`∃ S` + 公共参数 + 缺的字段 ⇒ A12′ -/

/-- **consumer / 缺口清单**：`pBase` 满足 P3 / hprof（参数选择）、`C.epsilon_cone`（P4）已由 astra 给；
`hext` 是**扩充后的 outer tuple 应当输出的形状**——同一个 `(F, q, κ, records)` 上，W1 的核心合取项
（narrow tuple 已给）再加上 astra **没有**的 8 项：S8（P6 的 `A > 1`）、S10（P1 的 link）、
S11（P2，producer = astra DiagonalDerivative，未落地）、S14（P5Linked）、S15（P6 `(b)`）、
S16（hStrong v2）、S17（Compat）、S19（RFC-a）。给定这些即得 `A12EnhancedConclusion_C11E`。 -/
theorem a12Enhanced_of_chain_C11P2 {pBase : CutoffParameters}
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
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupply_C11E F q) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨_, F, q, κ, records, ε, C1, C2, -, rfl, ⟨hfixed, hrad, hord, hacc⟩, hconst, hκ, hκanti,
    hδanti, hρanti, hcan, hnc, hδlim, hrecent, hS8, hP1, hP2, hP5, hP6, hStrong, hCompat,
    hRFC⟩ := hext
  refine exists_surgery_with_decaying_accuracy_enhanced_of_supplies_C11E P g
    ⟨F, q, records, _, C1, C2, κ, diagonalAccuracy_C11S q.delta, C.Ctime,
      ⟨supply1_of_astra_C11A q hδanti hδlim, hρanti, hconst,
        supply5_of_astra_C11A F q _ C1 C2 hcan, supply6_of_astra_C11A F κ _ hκ hκanti hnc,
        supply7_of_astra_C11A q hδanti, hS8, hrecent⟩,
      hP1, hP2, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
      coneEpsilonSupply_of_closedBirth_C11P2 C, hP5, hP6, hStrong, hCompat,
      modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof, hRFC⟩

end GC.LongTime.Ch11
