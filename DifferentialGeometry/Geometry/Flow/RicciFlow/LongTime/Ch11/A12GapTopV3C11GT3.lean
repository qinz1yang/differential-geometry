import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV2C11GT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopPBaseC11GT3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopLinkedC11GT3

set_option autoImplicit false

/-!
# S-CH11-GAPTOP3 G3：A12′ 顶层缺口定理第三版 `a12EnhancedFull_of_gaps_v3_C11GT3`（后缀 `_C11GT3`）

`a12EnhancedFull_of_gaps_v2_C11GT2`（不改）的 `hpbase` 与 `hlinkfine` 两个 binder 用树内产物实例化：

* `hpbase` := `hpbase_of_provider_C11GT3 P g`（G1：W6 byPoint 的 collar 保留版，collar 条取自 PBASE 的
  strong provider 槽，无 drift，无 adapter）；
* `hlinkfine` := `fun S => hlinkfine_of_chain_C11GT3 S`（G2：S10 落树后 `LinkedAndFine_C11GT2 S` 无条件，
  `hlinkS10 := linkedWindowsSupply_of_chain_C11SL`，`hfine_S14 := lateLinkedHlink_of_chain_C11SL`）。

所以 v3 的 binder 列表（逐字、可 grep）只剩

`hK  hspine  hP6b  hfull`（**4 个**；v2 是 6 个，v1 是 7 个 + 自由参数 `εK hεK`）。

G1 / G2 **没有留下任何剩余前提**（G1 的 collar 条不再是显式假设；G2 的 `hlink` 是 chain 的结构字段），
所以 v3 里没有额外的 G1/G2 binder。四个 binder 的类型与 v2 逐字相同（从 v2 复制，`hK` 仍是 budget
形 + `hguard`，`hP6b : CanonicalLateCore_P6X` 形，各自带 `∃ ε_i`），结论仍是
`A12EnhancedFullConclusion_C11F P g`，
下游（consumer example 核）与 v2 同形。证明体 = v2 顶层定理应用于 G1 / G2 的两个实例。

仍开的义务（A12′ 的剩余缺口，**本文件不证**）：`hK`（κ 线 budget 形，KWRAP / `hsmallScale` / hseedWin）、
`hspine`（(c) = (b) + 种子尺度）、`hP6b`（`CanonicalLateCore_P6X`，hscalU / D-17 / S-c 等）、`hfull`
（S16 三轮进树后另开 G4）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-- **A12′ v3 顶层缺口定理，第三版**：binder `hK hspine hP6b hfull`（4 个）。`hpbase`（G1）与
`hlinkfine`（G2）已由树内产物供给；四个剩余 binder 的类型与 v2 逐字相同。 -/
theorem a12EnhancedFull_of_gaps_v3_C11GT3 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hK : ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      (∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
        q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
          diagonalAccuracy_C11S q.delta A
            ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
        A < 12 * (3 : ℝ) ^ m) →
      pB.modelAccuracy ≤ εκ Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A → (∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
          (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))))
    (hfull : ∃ εfull : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εfull Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εfull Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
        ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
        ∃ W : SpatialCanonicalWitness s.metric Γ.epsilon (max Γ.C1s Γ.Cbirth)
            (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart Γ.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ)
              (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
              (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
                G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
              s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G Γ.epsilon x
                s.time) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v2_C11GT2 P g (hpbase_of_provider_C11GT3 P g) hK hspine hP6b
    (fun S => hlinkfine_of_chain_C11GT3 S) hfull

/-- consumer：v3 顶层定理的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`
（与 v1 / v2 同一结论类型，下游不变）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：顶层定理的签名稳定（binder 列表即 `type_of%`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_v3_C11GT3 P g) := a12EnhancedFull_of_gaps_v3_C11GT3 P g

end GC.LongTime.Ch11
