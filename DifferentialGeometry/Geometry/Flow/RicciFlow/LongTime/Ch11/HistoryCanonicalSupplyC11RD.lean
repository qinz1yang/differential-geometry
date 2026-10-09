import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryCanonicalTransportC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CanonicalConstantsC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing

set_option autoImplicit false

/-!
# S-CH11-REPROVE-D (G3)：S5 `HistoryCanonicalSupply_C11S` 的组装

G2 给出对任意历史的 canonical 传输核。这里把它们接到 `SurgerySuppliesC11S` 冻结的 S5 陈述
`HistoryCanonicalSupply_C11S F ρ ε C1 C2`（W1 的 history 形 canonical 合取项）：

* `parameter_compat_of_successors_C11RD`：`ScaffoldData.all_parameter_values_of_successors` 的树内重证
  （相邻参数一致 ⇒ `diagonal_eq_on_prefix` 需要的 `hcompat`）；
* `historyCanonicalSupply_of_diagonal_C11RD`：`exists_surgery_with_spatial_control` 末段的 canonical
  合取项：第 `n` 个观测历史上用 `(p n).neckRadius` 的 canonical ⇒ 用 `(diagonal p).neckRadius` 的 S5；
* `historyCanonicalSupply_of_states_C11RD`：`observation_canonical` + diagonal：
  `F.tower.history n = (Hs n).restrict (a n)`（`Hs n` 是 `t < E n` 上 canonical 的完整历史，
  `a n < E n`）⇒ S5；
* `historyCanonicalSupply_of_chain_C11RD`：对 astra `PreparedSpatialChain` 形的历史链
  （`E 0 = 0`，相邻 step 数据，closed receiver `closed`）直接给 S5；
* `canonicalSupply_of_chain_C11RD`：再经 `canonicalSupply_of_history_C11S` 给 postMetric 形
  `CanonicalSupply_C11S`（A12 的 `canonical` 字段形）。

对应 astra 链：`PreparedSpatialChain`（state `n + 1` 的 `history`、`parameters`）→ `observation`
（`restrict ⟨n, _⟩`）→ `exists_surgery_with_spatial_control`。**仍是显式 binder 的物理输入** =
`closed`（每步 closed-seam receiver，见 G2 / G4）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-! ## 参数相容（`ScaffoldData.all_parameter_values_of_successors`） -/

/-- 相邻参数在 `t ≤ n` 上一致 ⇒ 一切 `m ≤ n` 在 `t ≤ m` 上一致（`diagonal_eq_on_prefix` 的 `hcompat`）。 -/
theorem parameter_compat_of_successors_C11RD (p : ℕ → CutoffParameters)
    (hnext : ∀ n : ℕ, ∀ t : ℝ, t ≤ (n : ℝ) →
      (p (n + 1)).delta t = (p n).delta t ∧
      (p (n + 1)).neckRadius t = (p n).neckRadius t ∧
      (p (n + 1)).protectedRadius t = (p n).protectedRadius t) :
    ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t ∧ (p m).neckRadius t = (p n).neckRadius t ∧
      (p m).protectedRadius t = (p n).protectedRadius t := by
  intro m n hmn t ht
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n hmn ih =>
    have htn : t ≤ (n : ℝ) := ht.2.trans (by exact_mod_cast hmn)
    obtain ⟨hd, hr, hp⟩ := hnext n t htn
    exact ⟨ih.1.trans hd.symm, ih.2.1.trans hr.symm, ih.2.2.trans hp.symm⟩

/-! ## diagonal：第 `n` 个观测历史用 `(p n).neckRadius` ⇒ `diagonal` -/

/-- `exists_surgery_with_spatial_control` 的 canonical 合取项：第 `n` 个观测历史上用 `(p n).neckRadius`
的 canonical，参数相容 ⇒ S5（阈值取 `(diagonal p).neckRadius`）。 -/
theorem historyCanonicalSupply_of_diagonal_C11RD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t ∧ (p m).neckRadius t = (p n).neckRadius t ∧
      (p m).protectedRadius t = (p n).protectedRadius t) {ε C1 C2 : ℝ}
    (hobs : ∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε) :
    HistoryCanonicalSupply_C11S F (CutoffParameters.diagonal p).neckRadius ε C1 C2 := by
  intro n t x hx
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) (n : ℝ) :=
    ⟨t.2.1, t.2.2.trans (F.tower.horizon_eq n).le⟩
  rw [(CutoffParameters.diagonal_eq_on_prefix p hcompat n ht).2.1] at hx
  exact hobs n t x hx

/-! ## restrict-of-states：`observation_canonical` + diagonal -/

/-- `observation_canonical` + diagonal：`F.tower.history n = (Hs n).restrict (a n)`，`Hs n` 在
`t < E n` 上（阈值 `(p n).neckRadius`）canonical，`a n < E n` ⇒ S5。 -/
theorem historyCanonicalSupply_of_states_C11RD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t ∧ (p m).neckRadius t = (p n).neckRadius t ∧
      (p m).protectedRadius t = (p n).protectedRadius t)
    (Hs : ℕ → RetainedCoreHistory.{u}) (a : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (E : ℕ → ℝ)
    (hF : ∀ n, F.tower.history n = (Hs n).restrict (a n)) (haE : ∀ n, ((a n : ℝ)) < E n)
    {ε C1 C2 : ℝ}
    (hstate : ∀ (n : ℕ) (t : Icc (0 : ℝ) (Hs n).toHistory.horizon), (t : ℝ) < E n →
      ∀ x : ((Hs n).toHistory.stageAt t).Carrier,
        ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((Hs n).toHistory.stageMetric ((Hs n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((Hs n).toHistory.stageMetric ((Hs n).toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) :
    HistoryCanonicalSupply_C11S F (CutoffParameters.diagonal p).neckRadius ε C1 C2 := by
  refine historyCanonicalSupply_of_diagonal_C11RD F p hcompat ?_
  intro n
  have key : ∀ J : RetainedCoreHistory.{u}, J = (Hs n).restrict (a n) →
      ∀ (t : Icc (0 : ℝ) J.toHistory.horizon) (x : (J.toHistory.stageAt t).Carrier),
        ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε := by
    rintro J rfl
    exact canonical_restrict_C11RD (Hs n) (a n) (p n).neckRadius (E n) (haE n) (hstate n)
  exact key _ (hF n)

/-! ## 链：`PreparedSpatialChain` 形 -/

/-- **链形 S5**：历史链 `H`（`horizon = E`，`E 0 = 0`，参数 `ps`，相邻 step 数据，closed receiver）
与观测塔 `F.tower.history n = (H (n + 1)).restrict (a n)`（`a n = n < E (n + 1)`）⇒ S5，
阈值取 `diagonal (fun n => ps (n + 1))`。astra 对应：`state m` 的 `history / parameters`、
`observation`、`exists_surgery_with_spatial_control`。 -/
theorem historyCanonicalSupply_of_chain_C11RD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ps : ℕ → CutoffParameters)
    (H : ℕ → RetainedCoreHistory.{u}) (E Q b : ℕ → ℝ) {ε C1 C2 : ℝ}
    (hE0 : E 0 = 0) (hHE : ∀ n, (H n).horizon = E n)
    (hEnonneg : ∀ n, 0 ≤ E n) (hEB : ∀ n, E n < E (n + 1)) (hbE : ∀ n, b n ≤ E n)
    (hprefix : ∀ n, (H n).toHistory.IsPrefixOf (H (n + 1)).toHistory)
    (hpast : ∀ n (t : ℝ), t ≤ E n →
      (ps (n + 1)).delta t = (ps n).delta t ∧
      (ps (n + 1)).neckRadius t = (ps n).neckRadius t ∧
      (ps (n + 1)).protectedRadius t = (ps n).protectedRadius t)
    (hthr : ∀ n (t : ℝ), E n ≤ t → t < E (n + 1) → Q n ≤ ((ps (n + 1)).neckRadius t ^ 2)⁻¹)
    (closed : ∀ n, ∀ T : Icc (0 : ℝ) (H (n + 1)).horizon, (T : ℝ) < (H (n + 1)).horizon →
      ∀ t : Icc (0 : ℝ) ((H (n + 1)).restrict T).toHistory.horizon, b n ≤ (t : ℝ) →
        ∀ x : (((H (n + 1)).restrict T).toHistory.stageAt t).Carrier,
          Q n < metricScalarAt
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) ε C1 C2 x,
            W.capTubeHasNeckChart ε)
    (a : ∀ n, Icc (0 : ℝ) (H (n + 1)).horizon) (ha : ∀ n, ((a n : ℝ)) = n)
    (hnE : ∀ n : ℕ, (n : ℝ) < E (n + 1))
    (hF : ∀ n, F.tower.history n = (H (n + 1)).restrict (a n)) :
    HistoryCanonicalSupply_C11S F
      (CutoffParameters.diagonal (fun n => ps (n + 1))).neckRadius ε C1 C2 := by
  have hchain := canonical_chain_C11RD H (fun n => (ps n).neckRadius) E Q b hE0 hHE hEnonneg hEB
    hbE hprefix (fun n t ht => (hpast n t ht).2.1) hthr closed
  refine historyCanonicalSupply_of_states_C11RD F (fun n => ps (n + 1))
    (parameter_compat_of_successors_C11RD _ fun n t ht => hpast (n + 1) t
      (ht.trans (hnE n).le))
    (fun n => H (n + 1)) a (fun n => E (n + 1)) hF (fun n => by rw [ha n]; exact hnE n) ?_
  intro n
  exact hchain (n + 1)

/-- **链形 S5，postMetric 形**：A12 `canonical` 字段的形（`canonicalSupply_of_history_C11S`）。 -/
theorem canonicalSupply_of_chain_C11RD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ps : ℕ → CutoffParameters)
    (H : ℕ → RetainedCoreHistory.{u}) (E Q b : ℕ → ℝ) {ε C1 C2 : ℝ}
    (hE0 : E 0 = 0) (hHE : ∀ n, (H n).horizon = E n)
    (hEnonneg : ∀ n, 0 ≤ E n) (hEB : ∀ n, E n < E (n + 1)) (hbE : ∀ n, b n ≤ E n)
    (hprefix : ∀ n, (H n).toHistory.IsPrefixOf (H (n + 1)).toHistory)
    (hpast : ∀ n (t : ℝ), t ≤ E n →
      (ps (n + 1)).delta t = (ps n).delta t ∧
      (ps (n + 1)).neckRadius t = (ps n).neckRadius t ∧
      (ps (n + 1)).protectedRadius t = (ps n).protectedRadius t)
    (hthr : ∀ n (t : ℝ), E n ≤ t → t < E (n + 1) → Q n ≤ ((ps (n + 1)).neckRadius t ^ 2)⁻¹)
    (closed : ∀ n, ∀ T : Icc (0 : ℝ) (H (n + 1)).horizon, (T : ℝ) < (H (n + 1)).horizon →
      ∀ t : Icc (0 : ℝ) ((H (n + 1)).restrict T).toHistory.horizon, b n ≤ (t : ℝ) →
        ∀ x : (((H (n + 1)).restrict T).toHistory.stageAt t).Carrier,
          Q n < metricScalarAt
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) ε C1 C2 x,
            W.capTubeHasNeckChart ε)
    (a : ∀ n, Icc (0 : ℝ) (H (n + 1)).horizon) (ha : ∀ n, ((a n : ℝ)) = n)
    (hnE : ∀ n : ℕ, (n : ℝ) < E (n + 1))
    (hF : ∀ n, F.tower.history n = (H (n + 1)).restrict (a n)) :
    CanonicalSupply_C11S F (CutoffParameters.diagonal (fun n => ps (n + 1))).neckRadius
      ε C1 C2 :=
  canonicalSupply_of_history_C11S F _ ε C1 C2
    (historyCanonicalSupply_of_chain_C11RD F ps H E Q b hE0 hHE hEnonneg hEB hbE hprefix hpast
      hthr closed a ha hnE hF)

/-! ## Consumer：A12 总装 `hconst` 与 `hcan` 由本车道给出 -/

/-- consumer：`exists_surgery_with_decaying_accuracy_of_data_C11S` 的 `hconst`（G1 的 `max` 形常数）
与 `hcan`（链形 S5 的 postMetric 形）由本车道给出，其余供给仍是显式 binder；`q := diagonal ..`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (ps : ℕ → CutoffParameters) (H : ℕ → RetainedCoreHistory.{u}) (E Q b : ℕ → ℝ)
    {ε C1s C2s Cbirth Cgrad : ℝ} (hε : 0 < ε) (hεs : ε < 1 / 100) (hC1s : 1 ≤ C1s)
    (hC2s : 1 ≤ C2s)
    (hE0 : E 0 = 0) (hHE : ∀ n, (H n).horizon = E n)
    (hEnonneg : ∀ n, 0 ≤ E n) (hEB : ∀ n, E n < E (n + 1)) (hbE : ∀ n, b n ≤ E n)
    (hprefix : ∀ n, (H n).toHistory.IsPrefixOf (H (n + 1)).toHistory)
    (hpast : ∀ n (t : ℝ), t ≤ E n →
      (ps (n + 1)).delta t = (ps n).delta t ∧
      (ps (n + 1)).neckRadius t = (ps n).neckRadius t ∧
      (ps (n + 1)).protectedRadius t = (ps n).protectedRadius t)
    (hthr : ∀ n (t : ℝ), E n ≤ t → t < E (n + 1) → Q n ≤ ((ps (n + 1)).neckRadius t ^ 2)⁻¹)
    (closed : ∀ n, ∀ T : Icc (0 : ℝ) (H (n + 1)).horizon, (T : ℝ) < (H (n + 1)).horizon →
      ∀ t : Icc (0 : ℝ) ((H (n + 1)).restrict T).toHistory.horizon, b n ≤ (t : ℝ) →
        ∀ x : (((H (n + 1)).restrict T).toHistory.stageAt t).Carrier,
          Q n < metricScalarAt
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t)
            ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
            W.capTubeHasNeckChart ε)
    (a : ∀ n, Icc (0 : ℝ) (H (n + 1)).horizon) (ha : ∀ n, ((a n : ℝ)) = n)
    (hnE : ∀ n : ℕ, (n : ℝ) < E (n + 1))
    (hF : ∀ n, F.tower.history n = (H (n + 1)).restrict (a n))
    (records : CutoffRecords_C11S F (CutoffParameters.diagonal fun n => ps (n + 1)))
    (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hδ : AccuracyDecaySupply_C11S (CutoffParameters.diagonal fun n => ps (n + 1)).delta)
    (hrad : RadiusAntitoneSupply_C11S (CutoffParameters.diagonal fun n => ps (n + 1)))
    (hwin : CanonicalWindowsSupply_C11S records)
    (hnc : NoncollapseSupply_C11S F κ ε)
    (hacc : LargerBallAccuracySupply_C11S
      (CutoffParameters.diagonal fun n => ps (n + 1)).delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F
      (CutoffParameters.diagonal fun n => ps (n + 1)).delta α)
    (hrcs : RecentCutoffSupply_C11S records) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_data_C11S F
    (CutoffParameters.diagonal fun n => ps (n + 1)) records ε (max C1s Cbirth)
    (max C2s (max Cbirth Cgrad)) κ α hδ hrad hwin
    (canonicalConstantsSupply_of_closedBirth_C11RD hε hεs hC1s hC2s)
    (canonicalSupply_of_chain_C11RD F ps H E Q b hE0 hHE hEnonneg hEB hbE hprefix hpast hthr
      closed a ha hnE hF)
    hnc hacc hLB hrcs

end GC.LongTime.Ch11
