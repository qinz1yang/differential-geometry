import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialExistence

set_option autoImplicit false

/-!
# O-CH11-ASM (G7)：A12 ⇐ S8 only（经已落地的 astra `PreparedSpatialExistence`）

donor 终形 `GC.GeneralFlow.exists_prepared_spatial_chains_from_initial`（ch11src
`SH/PreparedSpatialExistence.lean:51`，无前提）：`∃ C, ∀ P g, ∃ pBase base, … ∀ budget > 0, ∃ S, …`。
`…_existence_core_C11A` 把它作为显式 `hE`（陈述逐字，量词顺序 `∃ C` 在 `∀ P g` 之前、`∀ budget`
在 `∃ pBase base` 之后）；主定理 `exists_surgery_with_decaying_accuracy_of_existence_C11A` 用该定理
填 `hE`，前提**只剩** `hP6`：对 Existence 给出的 `C, pBase, base`，P6 选一个正的 accuracy budget，
使服从它的 chain 在自己的 tower 与对角 δ 上满足 S8（KL 式"δ 按 A 请求下跌"，design §3）。

外审 R-C11-3 口径（`out/dispositions-R-C11-3-outer-block-step.md`）：
* D-R-C11-3-9：S8 绑定**同一 tower / 对角 δ**——`hP6` 的结论是
  `∀ F, F.tower = S.tower → LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta …`
  （= G6 `exists_surgery_with_decaying_accuracy_of_chain_C11A` 的 of_chain 形）。
* D-R-C11-3-10：只对**带证书的输出 tower** 陈述 S8（chain 以 `base` 起步且服从 P6 选的 budget）；
  全称变体 `…_allChains_C11A` 合法但过强，只作便利入口。
* D-R-C11-3-8 ③：生产者被**消费**——主定理与对齐 `example` 都由落地的
  `exists_prepared_spatial_chains_from_initial` 实例化；`…_core_C11A` 的显式 `hE` 只是中间层。
  本文件走 `∃ S` 路线，与 OUTER 车道的 `∀ X σ, Inv → Ready → ∃ Y d`（BlockStep）路线互不冒充。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set

namespace GC.LongTime.Ch11

universe u

/-- S8 的 P6 形（**只此一个前提**）：对 Existence 给出的常数 `C`、基参数 `pBase`、base state，
存在一个正的 accuracy budget，使所有服从该 budget 的 chain 在自己的 tower 与对角 δ 上满足 S8。 -/
theorem exists_surgery_with_decaying_accuracy_of_existence_core_C11A
    (hE : ∃ C : GC.GeneralFlow.ClosedBirthConstants,
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
      ∃ (pBase : CutoffParameters) (base : GC.GeneralFlow.PreparedSpatialState pBase C P g 0 1),
        base.history = RetainedCoreHistory.atZero P g ∧ base.radius ≤ 1 ∧
        ∀ (budget : ∀ (n : ℕ)
        (L : GC.GeneralFlow.PreparedSpatialState pBase C P g
          (GC.GeneralFlow.preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
        GC.GeneralFlow.ClosedBirthPreparedClass pBase C
          (L.native.stage (Fin.last L.native.eventCount))
          (L.native.initialMetric (Fin.last L.native.eventCount))
          ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
        (∀ n L future r, 0 < budget n L future r) →
      ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
        S.state 0 = base ∧
        ∀ n, ∃ (future : GC.GeneralFlow.ClosedBirthPreparedClass pBase C
            ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
            ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
            ((3 : ℝ) ^ (n + 1) -
              (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
          0 < r ∧ (S.state (n + 1)).radius = r ∧
          HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hP6 : ∀ (C : GC.GeneralFlow.ClosedBirthConstants) (pBase : CutoffParameters)
      (base : GC.GeneralFlow.PreparedSpatialState pBase C P g 0 1),
      ∃ (budget : ∀ (n : ℕ)
        (L : GC.GeneralFlow.PreparedSpatialState pBase C P g
          (GC.GeneralFlow.preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
        GC.GeneralFlow.ClosedBirthPreparedClass pBase C
          (L.native.stage (Fin.last L.native.eventCount))
          (L.native.initialMetric (Fin.last L.native.eventCount))
          ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
        (∀ n L future r, 0 < budget n L future r) ∧
        ∀ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g, S.state 0 = base →
          (∀ n, ∃ (future : GC.GeneralFlow.ClosedBirthPreparedClass pBase C
              ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
              ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
              ((3 : ℝ) ^ (n + 1) -
                (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
            0 < r ∧ (S.state (n + 1)).radius = r ∧
            HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r) →
          ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
            LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
              (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ := by
  obtain ⟨C, hC⟩ := hE
  obtain ⟨pBase, base, -, -, hchain⟩ := hC P g
  obtain ⟨budget, hpos, hS8⟩ := hP6 C pBase base
  obtain ⟨S, hS0, hS⟩ := hchain budget hpos
  exact exists_surgery_with_decaying_accuracy_of_chain_C11A S (hS8 S hS0 hS)

/-- **A12 ⇐ S8 only**（G7 主定理）：结论与 A12 逐字相同；`hE` 由落地的 donor 定理填（D-R-C11-3-8 ③），
`hP6` 是 D-R-C11-3-9 的同 tower / 对角 δ 形，只对带 budget 证书的输出 chain（D-R-C11-3-10）。 -/
theorem exists_surgery_with_decaying_accuracy_of_existence_C11A
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hP6 : ∀ (C : GC.GeneralFlow.ClosedBirthConstants) (pBase : CutoffParameters)
      (base : GC.GeneralFlow.PreparedSpatialState pBase C P g 0 1),
      ∃ (budget : ∀ (n : ℕ)
        (L : GC.GeneralFlow.PreparedSpatialState pBase C P g
          (GC.GeneralFlow.preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
        GC.GeneralFlow.ClosedBirthPreparedClass pBase C
          (L.native.stage (Fin.last L.native.eventCount))
          (L.native.initialMetric (Fin.last L.native.eventCount))
          ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
        (∀ n L future r, 0 < budget n L future r) ∧
        ∀ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g, S.state 0 = base →
          (∀ n, ∃ (future : GC.GeneralFlow.ClosedBirthPreparedClass pBase C
              ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
              ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
              ((3 : ℝ) ^ (n + 1) -
                (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
            0 < r ∧ (S.state (n + 1)).radius = r ∧
            HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r) →
          ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
            LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
              (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_existence_core_C11A
    GC.GeneralFlow.exists_prepared_spatial_chains_from_initial.{u} P g hP6

/-- 便利变体：S8 对**所有** chain 成立（budget 取常值 1）。D-R-C11-3-10：合法但过强。 -/
theorem exists_surgery_with_decaying_accuracy_of_existence_allChains_C11A
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hP6 : ∀ (C : GC.GeneralFlow.ClosedBirthConstants) (pBase : CutoffParameters)
      (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g),
      ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_existence_C11A P g fun C pBase _ =>
    ⟨fun _ _ _ _ => 1, fun _ _ _ _ => one_pos, fun S _ _ => hP6 C pBase S⟩

/-- 逐字对齐（消费生产者，D-R-C11-3-8 ③）：G7 主定理（budget 形 `hP6`）的结论类型就是 A12。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hP6 : ∀ (C : GC.GeneralFlow.ClosedBirthConstants) (pBase : CutoffParameters)
      (base : GC.GeneralFlow.PreparedSpatialState pBase C P g 0 1),
      ∃ (budget : ∀ (n : ℕ)
        (L : GC.GeneralFlow.PreparedSpatialState pBase C P g
          (GC.GeneralFlow.preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
        GC.GeneralFlow.ClosedBirthPreparedClass pBase C
          (L.native.stage (Fin.last L.native.eventCount))
          (L.native.initialMetric (Fin.last L.native.eventCount))
          ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) → ℝ → ℝ),
        (∀ n L future r, 0 < budget n L future r) ∧
        ∀ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g, S.state 0 = base →
          (∀ n, ∃ (future : GC.GeneralFlow.ClosedBirthPreparedClass pBase C
              ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
              ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
              ((3 : ℝ) ^ (n + 1) -
                (S.state n).history.time (Fin.last (S.state n).history.eventCount))) (r : ℝ),
            0 < r ∧ (S.state (n + 1)).radius = r ∧
            HEq (S.state (n + 1)).prepared future ∧ S.accuracy n ≤ budget n (S.state n) future r) →
          ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
            LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
              (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_existence_C11A P g hP6

end GC.LongTime.Ch11
