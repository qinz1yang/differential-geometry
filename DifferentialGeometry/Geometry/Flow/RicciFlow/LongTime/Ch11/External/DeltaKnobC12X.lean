import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.PBaseC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialLargerBallAccuracy

set_option autoImplicit false

/-!
# S-C12X-DIAG (G3)：δ 旋钮——chain 的 `q.delta` 的上界来自 astra 的 `budget`（后缀 `_C12X`）

S17 的 producer `compatibleCapsSupply_of_astra_C12X` 的参数形前提 `q.delta 0 ≤ 1/8646` **对 astra 的
链不可满足**：存在性定理的 base 的 `delta ≡ 1/2`（`PreparedSpatialProviders…` 的初态陈述
`S.parameters.delta = fun _ => 1/2`），而 `PreparedSpatialSuccessor.parameters_past` 把 `t ≤ E` 上的
`delta` 原样传给后继，所以对角 `(chainDiagonal_C11A S).delta 0 = 1/2`（`chainDiagonal_delta_zero_C12X`）。

真正的旋钮是 `t > 0` 上的 δ：`diagonal_delta_eq_accuracy_on_block`（astra）说 `(0, ∞)` 上对角 `delta`
在几何块 `(horizon n, 3ⁿ]` 上等于 `S.accuracy n`；`S.accuracy n ≤ budget n _ _ _`，而 `budget` 是 existence
的**输入**（任意正函数）。取 `budget ≡ δ₀` 得 `∀ n, S.accuracy n ≤ δ₀`，于是对角 `delta` 在 `t > 0` 上 `≤ δ₀`，
而 event 时刻严格正（`time_strictMono` + `time_zero`），所以 S17 的 event-δ 形前提
`q.delta ((F.tower.history n).time i.succ) ≤ 1/8646`（`compatibleCapsSupply_of_eventDelta_C12X`）取
`δ₀ := 1/8646` 即得。

* `chainDiagonal_delta_zero_C12X`：对角 `delta 0 = 1/2`（参数形前提不可满足的原因）；
* `chainDiagonal_delta_le_of_accuracy_C12X`：`∀ n, S.accuracy n ≤ δ₀` ⇒ `∀ t > 0, 对角 delta t ≤ δ₀`；
* `exists_prepared_chains_accuracy_le_C12X`：`exists_prepared_spatial_chains_from_initial_pBase_C12X`
  的再加强：chain 额外满足 `∀ n, S.accuracy n ≤ δ₀`（`δ₀ > 0` 任取）；
* `exists_w1_params_eventDelta_C12X`：`w1_params_of_preparedSpatialChain_C11P2` 的全部结论，同一
  `(F, q, κ, records)` 上加 event-δ 合取项 `∀ n i, q.delta ((F.tower.history n).time i.succ) ≤ δ₀`。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- 对角 `delta` 在 `0` 处等于 `state 0` 的 `delta 0`（`parameters_past`，`t = 0 ≤ horizon 0 = 0`）：
astra 的 base 有 `delta ≡ 1/2`，故 `q.delta 0 = 1/2`，`q.delta 0 ≤ 1/8646` 不可满足。 -/
theorem chainDiagonal_delta_zero_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g) :
    (chainDiagonal_C11A S).delta 0 = (S.state 0).parameters.delta 0 := by
  change (S.state (Nat.ceil (0 : ℝ) + 1)).parameters.delta 0 = (S.state 0).parameters.delta 0
  rw [Nat.ceil_zero]
  exact ((S.successor 0).parameters_past 0 (by norm_num [preparedSpatialHorizon])).1

/-- `∀ n, S.accuracy n ≤ δ₀` ⇒ 对角 `delta` 在 `t > 0` 上 `≤ δ₀`（块 `(horizon n, 3ⁿ]` 上等于
`S.accuracy n`）。 -/
theorem chainDiagonal_delta_le_of_accuracy_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (δ₀ : ℝ) (hacc : ∀ n, S.accuracy n ≤ δ₀)
    (t : ℝ) (ht : 0 < t) : (chainDiagonal_C11A S).delta t ≤ δ₀ := by
  have hex : ∃ n : ℕ, t ≤ (3 : ℝ) ^ n :=
    ⟨Nat.ceil t, (Nat.le_ceil t).trans (nat_lt_three_pow (Nat.ceil t)).le⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, t ≤ (3 : ℝ) ^ n ∧ ∀ m : ℕ, m < n → ¬ t ≤ (3 : ℝ) ^ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hlow : preparedSpatialHorizon n < t := by
    cases n with
    | zero => exact ht
    | succ n => exact lt_of_not_ge (hmin n (Nat.lt_succ_self n))
  exact (PreparedSpatialChain.diagonal_delta_eq_accuracy_on_block S n t hlow hn).trans_le (hacc n)

/-- 上一个定理 + event 时刻严格正：`F.tower` 任意，`q.delta = 对角 delta`（`[0, ∞)`）时，
event 时刻的 `q.delta ≤ δ₀`。 -/
theorem eventDelta_of_accuracy_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (δ₀ : ℝ) (hacc : ∀ n, S.accuracy n ≤ δ₀) (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters)
    (hdelta : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t) :
    ∀ n (i : Fin (F.tower.history n).eventCount),
      q.delta ((F.tower.history n).time i.succ) ≤ δ₀ := by
  intro n i
  have hpos : 0 < (F.tower.history n).time i.succ := by
    have h := (F.tower.history n).time_strictMono (Fin.succ_pos i)
    rwa [(F.tower.history n).time_zero] at h
  rw [hdelta _ hpos.le]
  exact chainDiagonal_delta_le_of_accuracy_C12X S δ₀ hacc _ hpos

/-- `exists_prepared_spatial_chains_from_initial_pBase_C12X` 的再加强：chain 的所有 accuracy `≤ δ₀`
（`budget ≡ δ₀`）。 -/
theorem exists_prepared_chains_accuracy_le_C12X (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ (fixed : StaticCapScaffold) (C : ClosedBirthConstants),
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ (pBase : CutoffParameters) (S : PreparedSpatialChain pBase C P g),
      pBase.fixed = fixed ∧ ModelConstraintsSupply_C11E pBase εProf_C11E.{u} ∧
      capWindowRadius_C11E + 1 ≤ pBase.modelRadius ∧ ∀ n, S.accuracy n ≤ δ₀ := by
  obtain ⟨fixed, C, hex⟩ := exists_prepared_spatial_chains_from_initial_pBase_C12X.{u}
  refine ⟨fixed, C, fun P g => ?_⟩
  obtain ⟨pBase, base, hfixed, hprof, hrad, -, -, hS⟩ := hex P g
  obtain ⟨S, -, hfut⟩ := hS (fun _ _ _ _ => δ₀) (fun _ _ _ _ => hδ₀)
  refine ⟨pBase, S, hfixed, hprof, hrad, fun n => ?_⟩
  obtain ⟨_, _, -, -, -, hle⟩ := hfut n
  exact hle

/-- **W1 + 参数级 enhanced 字段 + event-δ**：`w1_params_of_preparedSpatialChain_C11P2` 的全部结论，
外加同一 `(F, q)` 上的 `∀ n i, q.delta ((F.tower.history n).time i.succ) ≤ δ₀`（`hacc` 来自
`exists_prepared_chains_accuracy_le_C12X`）。 -/
theorem exists_w1_params_eventDelta_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (δ₀ : ℝ) (hacc : ∀ n, S.accuracy n ≤ δ₀) :
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
      ConeEpsilonSupply_C11E ε ∧
      ∀ n (i : Fin (F.tower.history n).eventCount),
        q.delta ((F.tower.history n).time i.succ) ≤ δ₀ := by
  obtain ⟨F, q, κ, records, ε, C1, C2, hTower, hε, hstat, hdelta, hconst, hκ, hκanti, hδanti,
    hρanti, hcan, hwin, hnc, hδlim, hrecent, hP3q, hprofq, hcone⟩ :=
    w1_params_of_preparedSpatialChain_C11P2 S hP3 hprof
  exact ⟨F, q, κ, records, ε, C1, C2, hTower, hε, hstat, hdelta, hconst, hκ, hκanti, hδanti,
    hρanti, hcan, hwin, hnc, hδlim, hrecent, hP3q, hprofq, hcone,
    eventDelta_of_accuracy_C12X S δ₀ hacc F q hdelta⟩

end GC.LongTime.Ch11
