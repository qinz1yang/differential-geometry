import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileFullC11F

set_option autoImplicit false

/-!
# O-C12X-RFCA (T4)：A12′ v2 的链级 consumer（后缀 `_C12X`）

`Ch11/EnhancedSuppliesFromAstraC11P2.lean` 的 `a12Enhanced_of_chain_C11P2` 结论是 PROF 形
`A12EnhancedConclusion_C11E`，其 `hext` 末项是 RFC-a 弱形 `FrontierCollarSupply_C11E F q`。
tracked admission（`Ch11/A12Enhanced.lean`）的陈述已是 v2 `A12EnhancedFullConclusion_C11F`
（MERGE U1：RFC-a 取 ch12 `hRFCa` 终端全称形 `FrontierCollarSupplyFull_C11F`）。树内没有 v2 的
"of supplies" 定理，这里补上：

* `EnhancedSurgeryProfile_C11E.toFull_C12X`：PROF 形 profile + 同一 profile 上的 RFC-a 全称形
  ⇒ v2 profile（旧字段不变，加 `frontier_collar_full`）；
* `a12EnhancedFull_of_chain_C12X`：同 `a12Enhanced_of_chain_C11P2`，`hext` 末项换成
  `FrontierCollarSupplyFull_C11F F q`（其余 19 项逐字不变），结论 `A12EnhancedFullConclusion_C11F P g`；
  证明：同一组 `(F, q, records)` 上走 `enhancedProfileOfSupplies_C11E`（旧 RFC-a 项由
  `frontierCollarSupply_of_full_C11F` 投影给出），再加全称形字段。

缺口清单（`hext` 中 astra 不给的 8 项）与 `a12Enhanced_of_chain_C11P2` 相同，只是 S19 换成全称形；
S19 全称形的无条件 producer 见 `Ch11/External/FrontierCollarFullC12X.lean`（T2）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter TopologicalSpace
open scoped Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- PROF 形 enhanced profile + **同一 profile** 上的 RFC-a 全称形 ⇒ v2 profile。 -/
def EnhancedSurgeryProfile_C11E.toFull_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (E : EnhancedSurgeryProfile_C11E F δ)
    (h : RFCaFull_C11F E.toAnalyticSurgeryProfile) : EnhancedSurgeryProfileFull_C11F F δ :=
  { toEnhancedSurgeryProfile_C11E := E
    frontier_collar_full := h }

/-- **A12′ v2 从链**：`∃ S` + 公共参数 P3 / hprof + `hext`（`a12Enhanced_of_chain_C11P2` 的 `hext`，
末项换成 RFC-a 全称形）⇒ `A12EnhancedFullConclusion_C11F P g`。 -/
theorem a12EnhancedFull_of_chain_C12X {pBase : CutoffParameters}
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
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupplyFull_C11F F q) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨_, F, q, κ, records, ε, C1, C2, -, rfl, ⟨hfixed, hrad, hord, hacc⟩, hconst, hκ, hκanti,
    hδanti, hρanti, hcan, hnc, hδlim, hrecent, hS8, hP1, hP2, hP5, hP6, hStrong, hCompat,
    hRFC⟩ := hext
  have hδ := supply1_of_astra_C11A q hδanti hδlim
  refine ⟨q.delta, F, hδ.1, hδ.2, ⟨EnhancedSurgeryProfile_C11E.toFull_C12X
    (enhancedProfileOfSupplies_C11E F q records _ C1 C2 κ (diagonalAccuracy_C11S q.delta) C.Ctime
      hρanti hconst (supply5_of_astra_C11A F q _ C1 C2 hcan)
      (supply6_of_astra_C11A F κ _ hκ hκanti hnc) (supply7_of_astra_C11A q hδanti) hS8 hrecent
      ⟨hP1, hP2, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
        coneEpsilonSupply_of_closedBirth_C11P2 C, hP5, hP6, hStrong, hCompat,
        modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
        frontierCollarSupply_of_full_C11F hRFC⟩) hRFC⟩⟩

/-- consumer：v2 链 ⇒ v2 结论 ⇒（投影）PROF 形结论、A12 的 `hasCommonNeckAccuracy`。 -/
example {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
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
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupplyFull_C11F F q) :
    A12EnhancedConclusion_C11E P g ∧
      ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
        (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  have hv2 := a12EnhancedFull_of_chain_C12X hP3 hprof hext
  refine ⟨a12EnhancedConclusion_of_full_C11F hv2, ?_⟩
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := hv2
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

end GC.LongTime.Ch11
