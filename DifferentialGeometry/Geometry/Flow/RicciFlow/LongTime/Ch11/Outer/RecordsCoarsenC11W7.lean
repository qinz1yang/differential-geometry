import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.ReserveByPointC11W6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CutoffRecordModelRestrictionC11RB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WideAlignC11V3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SuppliesOfAstraC11A

set_option autoImplicit false

/-!
# S-CH11-W1L7 (G1)：GAP-2b——records 粗化到精确半径 `D`，SMALLVOL3 入口吃 `D ≤ q.modelRadius`

OUTER G6 的 GAP-2b：SMALLVOL3 的入口 `localKappaWindow_zero_of_narrowTuple_records_C11V3` 要
`q.modelRadius = D`（等式），而 PCBC / narrow tuple 只给 `Dstar ≤ q.modelRadius`
（`q.modelRadius = pBase.modelRadius`，`pBase` 在 `εReserve` 之后才选出，不能反过来用它取 `D`）。
按 OUTER 建议 (b)，在 consumer 端把 records 粗化：

* `coarsenRecords_C11W7`：`restrictModelWindow_C11RB` 逐 record 作用，records 换到
  `q.withModelWindow_C11RB D m q.modelAccuracy …`（`modelRadius = D`、`modelOrder = m`、
  `modelAccuracy` 不变；`delta` / `neckRadius` / `protectedRadius` / `fixed` / `recenterConstant`
  都是 `rfl` 不变），`hasCanonicalWindow` 沿 `hasCanonicalWindow_restrictModelWindow_C11RB` 保持。
* `localKappaWindow_zero_of_narrowTuple_records_ge_C11W7`：SMALLVOL3 入口，`q.modelRadius = D`
  放宽成 `D ≤ q.modelRadius`（其余前提逐字同），由粗化 + 原入口得。
* `localKappaWindow_of_chain_C11W7`：任一 `S : PreparedSpatialChain pBase C P g`，只要
  `D ≤ pBase.modelRadius`、`pBase.modelAccuracy ≤ ε₀(D, C, N)`、`2 ≤ pBase.modelOrder`，narrow tuple 的
  `(F, q)`（`F.tower = S.tower`，`q.delta` / `q.neckRadius` 在 `[0, ∞)` 上等于 `S` 的对角）满足
  "K 链 wide supply ⇒ 对每个 `A > 0` 有 `nr := 0` window"。S7 由 `supplies_of_astra_C11A` 内部给，
  canonical windows / `HistoryCanonicalSupply` / 单调由 narrow tuple 内部给，`N` 无条件
  （`exists_uniform_stageDegreeBound_C11W7`，只依赖 `P`）。
* `a12_of_astra_byPoint_window_C11W7`：end-to-end。OUTER G6 `a12_of_astra_byPoint_C11W6` 的 S8
  前提 `hS8` 换成两个**显式缺口**：`hK`（K 链 `LocalKappaWideSupply_C11Q`，GAP-3，归 KAPPA）与
  `hclosure`（P6 收口：`nr := 0` window ⇒ S8，归 P6）。其余全部已支付：`BlockStep`（Step +
  Providers）、按点 `εReserve`（G6）、records 粗化（本文件）、SMALLVOL3（HI + 标量下界由 records 内部给）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. records 粗化 -/

/-- records 粗化：每个 selected record 换成 `D ≤ modelRadius`、`m ≤ modelOrder` 的更粗 static
model（accuracy 不变）。 -/
def coarsenRecords_C11W7 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {D : ℝ} {m : ℕ} (hD : 0 < D)
    (hDq : D ≤ q.modelRadius) (hm : m ≤ q.modelOrder) (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow) :
    CutoffRecords_C11S F (q.withModelWindow_C11RB D m q.modelAccuracy hD q.modelAccuracy_pos) :=
  fun n i => (records n i).restrictModelWindow_C11RB (hwin n i) hD hDq hm le_rfl

/-- 粗化后的 records 仍有 canonical window（窗口含 cap core：`transitionEnd < D + 1`）。 -/
theorem coarsenRecords_window_C11W7 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {D : ℝ} {m : ℕ} (hD : 0 < D)
    (hDq : D ≤ q.modelRadius) (hm : m ≤ q.modelOrder) (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hcap : StandardCap.transitionEnd < D + 1) :
    ∀ n i b, ((coarsenRecords_C11W7 hD hDq hm records hwin n i).static b).hasCanonicalWindow :=
  fun n i b => (records n i).hasCanonicalWindow_restrictModelWindow_C11RB (hwin n i) hD hDq hm
    le_rfl hcap b

/-- consumer：粗化给精确半径 `D`，且 `delta` / `neckRadius` / `modelAccuracy` / canonical window 不变。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {D : ℝ} (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (hDq : D ≤ q.modelRadius) (hm : 2 ≤ q.modelOrder) (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow) :
    ∃ (q' : CutoffParameters) (records' : CutoffRecords_C11S F q'),
      q'.modelRadius = D ∧ q'.modelAccuracy = q.modelAccuracy ∧ q'.delta = q.delta ∧
      q'.neckRadius = q.neckRadius ∧ (∀ n i b, ((records' n i).static b).hasCanonicalWindow) := by
  have hte := StandardCap.transitionEnd_pos
  have hDpos : 0 < D := by linarith
  exact ⟨_, coarsenRecords_C11W7 hDpos hDq hm records hwin, rfl, rfl, rfl, rfl,
    coarsenRecords_window_C11W7 hDpos hDq hm records hwin (by linarith)⟩

/-- `N` 只依赖 `P`（不需要 `InCutoffClass`；`exists_stageDegreeBound_C11V3` 的 `P`-一致形）。 -/
theorem exists_uniform_stageDegreeBound_C11W7 (P : OrientedThreeStage.{u}) :
    ∃ N : ℕ, 0 < N ∧ ∀ {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ) (j),
      GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N := by
  obtain ⟨N, hN, hb⟩ := GC.GeneralFlow.initial_finite_freeFactor_bound P
  exact ⟨N, hN, fun F n j => GC.GeneralFlow.stage_degree_of_freeFactor_ancestry N hb
    (fun q => GC.GeneralFlow.retained_history_freeFactor (F.tower.history n) (F.tower.initial n) j
      q)⟩

/-! ## 2. SMALLVOL3 入口：`D ≤ q.modelRadius` -/

/-- **GAP-2b 修复**：SMALLVOL3 的 records 入口，`q.modelRadius = D` 放宽成 `D ≤ q.modelRadius`。 -/
theorem localKappaWindow_zero_of_narrowTuple_records_ge_C11W7 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      D ≤ q.modelRadius → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_records_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc hord records hwin hanti hcanon hdeg hS7 hwide
  have hte := StandardCap.transitionEnd_pos
  have hDpos : 0 < D := by linarith
  have hcap : StandardCap.transitionEnd < D + 1 := by linarith
  exact hE (q := q.withModelWindow_C11RB D 2 q.modelAccuracy hDpos q.modelAccuracy_pos) hA rfl
    hacc le_rfl (coarsenRecords_C11W7 hDpos hDq hord records hwin)
    (coarsenRecords_window_C11W7 hDpos hDq hord records hwin hcap) hanti hcanon hdeg hS7 hwide

/-! ## 3. narrow tuple 上的入口 -/

/-- 两个 `RawSurgery` 的 tower 相同则相等（第二个字段是 Prop）。 -/
theorem rawSurgery_ext_C11W7 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F F' : GC.Interface.RawSurgery P g} (h : F.tower = F'.tower) : F = F' := by
  cases F
  cases F'
  cases h
  rfl

/-- **chain 入口**：对 `C` 与 `D`、`N`，存在阈值 `ε₀`：任一 `S : PreparedSpatialChain pBase C P g`，
`D ≤ pBase.modelRadius`、`pBase.modelAccuracy ≤ ε₀`、`2 ≤ pBase.modelOrder`、`N` 是 `P` 的 stage 度数界
时，narrow tuple 的 `(F, q)`（`F.tower = S.tower`；`q.delta` / `q.neckRadius` 在 `[0, ∞)` 上等于 `S`
的对角）满足：K 链 wide supply（取 `δ := q.delta`、`α := diagonalAccuracy_C11S q.delta`、
`nr := q.neckRadius`）⇒ 每个 `A > 0` 有 `nr := 0` window。 -/
theorem localKappaWindow_of_chain_C11W7 (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D)
    (C : ClosedBirthConstants) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {pBase : CutoffParameters} {P : OrientedThreeStage.{u}} {g : P.Metric}
      (S : PreparedSpatialChain pBase C P g), D ≤ pBase.modelRadius →
      pBase.modelAccuracy ≤ ε₀ → 2 ≤ pBase.modelOrder →
      (∀ (F : GC.Interface.RawSurgery P g) (n : ℕ) (j),
        GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = S.tower ∧
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) ∧
        (LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
          ∀ A : ℝ, 0 < A → ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_records_ge_C11W7.{u} D hD
    C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase P g S hDp hacc hord hdeg
  obtain ⟨F, q, κ, records, hTower, ⟨-, hrad, hordq, haccq, -⟩, hκ, hκanti, hδanti, hρanti,
    hpref, -, hcan, hwin, hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  have hconst := canonicalConstantsSupply_of_closedBirthConstants_C11A C
  have hsup := supplies_of_astra_C11A F q κ records C.epsilon (max C.C1s C.Cbirth)
    (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) hconst hκ hκanti hδanti hρanti hcan hwin hnc hδlim
    hrecent
  refine ⟨F, q, hTower, fun t ht => ?_, fun hwide A hA => ?_⟩
  · have hmem : t ∈ Icc (0 : ℝ) (Nat.ceil t : ℝ) := ⟨ht, Nat.le_ceil t⟩
    exact ⟨(hpref (Nat.ceil t) t hmem).1, (hpref (Nat.ceil t) t hmem).2.1⟩
  · have hDq : D ≤ q.modelRadius := by
      rw [hrad]
      exact hDp
    have haccQ : q.modelAccuracy ≤ ε₀ := by
      rw [haccq]
      exact hacc
    have hordQ : 2 ≤ q.modelOrder := by
      rw [hordq]
      exact hord
    exact hE hA hDq haccQ hordQ records hwin hρanti hcan (hdeg F) hsup.2.2.2.2.2.2.1 hwide

/-! ## 4. end-to-end：S8 ⇐ K 链 + P6 收口（显式缺口） -/

/-- **A12（按点 εReserve + records 粗化 + SMALLVOL3；显式缺口 = K 链 + P6 收口）**。

OUTER G6 `a12_of_astra_byPoint_C11W6` 的 S8 前提被换成两个显式缺口，且只对满足 `pBase` 三个界
（accuracy ≤ `εK C`、radius ≥ `Dstar`、order ≥ 2）的 chain 陈述：
* `hK`（GAP-3，KAPPA K0–K6）：narrow tuple 的 `(F, q)` 上 `LocalKappaWideSupply_C11Q F q.delta
  (diagonalAccuracy_C11S q.delta) q.neckRadius`；
* `hclosure`（P6 收口）：每个 `A > 0` 的 `nr := 0` window ⇒ S8（of_chain 绑定形）。
SMALLVOL3 + 粗化 + narrow tuple 把 `hK` 变成 window；`rawSurgery_ext_C11W7` 把任意
`F.tower = S.tower` 的 `F` 识别成 narrow tuple 的 `F`。`εK` 是 K 链生产者需要的 accuracy 阈值（未知，
作参数），取 `εReq C := min (εK C) (ε₀ C)`。 -/
theorem a12_of_astra_byPoint_window_C11W7 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Dstar : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ Dstar) (cMax : ℝ) (hcMax : 0 < cMax)
    (εK : ClosedBirthConstants → ℝ) (hεK : ∀ C, 0 < εK C)
    (hK : ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
      (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters), F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pBase.modelAccuracy ≤ εK C → Dstar ≤ pBase.modelRadius → 2 ≤ pBase.modelOrder →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius)
    (hclosure : ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
      (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g),
      F.tower = S.tower → pBase.modelAccuracy ≤ εK C → Dstar ≤ pBase.modelRadius →
      2 ≤ pBase.modelOrder →
      (∀ A : ℝ, 0 < A → ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
      LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
        (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) := by
  have hte := StandardCap.transitionEnd_pos
  have hDstar : 0 < Dstar := by linarith
  obtain ⟨N, hN, hdegN⟩ := exists_uniform_stageDegreeBound_C11W7.{u} P
  have hex := fun C : ClosedBirthConstants => localKappaWindow_of_chain_C11W7.{u} Dstar hD C N hN
  let ε₀ : ClosedBirthConstants → ℝ := fun C => Classical.choose (hex C)
  have hε₀ : ∀ C, 0 < ε₀ C := fun C => (Classical.choose_spec (hex C)).1
  refine a12_of_astra_byPoint_C11W6 P g Dstar hDstar cMax hcMax (fun C => min (εK C) (ε₀ C))
    (fun C => lt_min (hεK C) (hε₀ C)) ?_
  intro Cdist C pBase X₀ hacc hrad hord _ _ _ T _ F hF
  have hacc₁ : pBase.modelAccuracy ≤ εK C := hacc.trans (min_le_left _ _)
  have hacc₂ : pBase.modelAccuracy ≤ ε₀ C := hacc.trans (min_le_right _ _)
  obtain ⟨F₀, q, hF₀, hq, himp⟩ := (Classical.choose_spec (hex C)).2 T.toChain hrad hacc₂ hord
    (fun F' n j => hdegN F' n j)
  have hFF : F = F₀ := rawSurgery_ext_C11W7 (hF.trans hF₀.symm)
  have hwin := himp (hK T.toChain F₀ q hF₀ hq hacc₁ hrad hord)
  rw [← hFF] at hwin
  exact hclosure T.toChain F hF hacc₁ hrad hord hwin

end GC.LongTime.Ch11
