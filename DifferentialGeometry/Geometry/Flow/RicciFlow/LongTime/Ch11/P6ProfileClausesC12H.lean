import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6FwdC11GT6

set_option autoImplicit false

/-!
# C12-9：A12′ 实际 chain 的 profile 条款——(b) producer、(c) 精确判据、(a) 搬运（后缀 `_C12H`）

**调用层（lead 补充裁定）**：顶层实际 q = SCRS⁺（`SameConstructionRetentionSupplyPlus_C11GT6 T`）∃ 解包出的
`q₀`；`T : BlockTower_C11W pB Γ P g …` 是 v6/v9/v10 冻结槽里 `∀ T`（带 `BudgetCertificate_C11GT2`）的 tower，
`q₀` 在 `[0, ∞)` 上等于 `chainDiagonal_C11A T.toChain`，且 `q₀.recenterConstant = pB.recenterConstant`。

* (b) **PROVED**（`obsLink_of_scrsPlus_C12H`）：SCRS⁺ 的 records 类型是 `CutoffRecords_C11S F₀ q₀`，即
  records 用的 `p n ≡ q₀`（常族），link 在 `t ≥ 0` 上逐字成立；另给 diag link、antitone 与 `δ → 0`。
  反面：`(S.observation n).parameters` 的**全局**形不成立（`not_obsLink_global_C12H`：
  `n = 0` 的观察参数在 `(0, ∞)` 上恒为 `accuracy 0 > 0`，与 `δ → 0` 矛盾）——只有前缀形。
* (c) **精确判据 PROVED / 全局形对实际 base REFUTED**：`recenter_q0_iff_base_C12H`
  `(∀ t ≥ 0, Λ·q₀.delta t ≤ 1/2) ↔ Λ·δ_{block 0}(0) ≤ 1/2`（`Λ = pB.recenterConstant`；
  `t > 0` 时 `δ = accuracy n ≤ δ_{block 0}(0)/4`，由 `cap_le_quarter` 逐块缩四倍）。树内 base
  （`PreparedSpatialBasePortC11P` l.70）取 `δ ≡ 1/2`，故 `Λ ≥ 4` 时全局 (c) 不成立
  （`not_recenter_global_of_half_C12H`）。另：SEPseq 那层的 `∀ q` 只锁 δ/ρ 不锁 `recenterConstant`，
  (c) 对 `∀ q` 不可能（`exists_recenter_bad_twin_C12H`）——所以 (c) 只能在 q₀ 层陈述。
* (a) **BLOCKED**：`PreparedSpatialChain` / `BlockTower_C11W` 没有任何字段把 `accuracy j` 与下一块半径
  `ρ_{j+1}` 联系起来（`BudgetCertificate` 的 cap 来自 `Classical.choose`）；这里只给搬运
  `hacc_of_chainDiagonal_C12H`（diag 上的 (a) ⇒ 任意 link 到 diag 的 q 上的 (a)）。
-/

noncomputable section

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-! ### §1 chain 的 delta 读出 -/

/-- 时间骨架：`b_n < b_{n+1}`（`_C12H`）。 -/
theorem preparedSpatialHorizon_lt_succ_C12H (n : ℕ) :
    preparedSpatialHorizon n < preparedSpatialHorizon (n + 1) := by
  cases n with
  | zero => norm_num [preparedSpatialHorizon]
  | succ k =>
    change (3 : ℝ) ^ k < 3 ^ (k + 1)
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self k)

/-- `state (N+1)` 的 delta 在 `t > 0` 处是某个 `accuracy n`（`n ≤ N`）（`_C12H`）。 -/
theorem chainState_delta_eq_accuracy_C12H (S : PreparedSpatialChain pBase C P g) (N : ℕ) :
    ∀ t : ℝ, 0 < t → ∃ n : ℕ, n ≤ N ∧ (S.state (N + 1)).parameters.delta t = S.accuracy n := by
  induction N with
  | zero =>
    intro t ht
    have hE : preparedSpatialHorizon 0 < t := by
      change (0 : ℝ) < t
      exact ht
    exact ⟨0, le_rfl, (S.successor 0).delta_after t hE⟩
  | succ N ih =>
    intro t ht
    by_cases hE : preparedSpatialHorizon (N + 1) < t
    · exact ⟨N + 1, le_rfl, (S.successor (N + 1)).delta_after t hE⟩
    · obtain ⟨n, hn, h⟩ := ih t ht
      refine ⟨n, hn.trans (Nat.le_succ N), ?_⟩
      rw [((S.successor (N + 1)).parameters_past t (not_lt.mp hE)).1, h]

/-- `chainDiagonal_C11A S` 的 delta 在 `t > 0` 处是某个 `accuracy n`（`_C12H`）。 -/
theorem chainDiagonal_delta_eq_accuracy_C12H (S : PreparedSpatialChain pBase C P g) {t : ℝ}
    (ht : 0 < t) : ∃ n : ℕ, (chainDiagonal_C11A S).delta t = S.accuracy n := by
  obtain ⟨n, -, h⟩ := chainState_delta_eq_accuracy_C12H S (Nat.ceil t) t ht
  exact ⟨n, h⟩

/-- `chainDiagonal_C11A S` 在 `t = 0` 处的 delta 是 base state 的 delta（`_C12H`）。 -/
theorem chainDiagonal_delta_zero_C12H (S : PreparedSpatialChain pBase C P g) :
    (chainDiagonal_C11A S).delta 0 = (S.state 0).parameters.delta 0 := by
  have h0 : (0 : ℝ) ≤ preparedSpatialHorizon 0 := le_of_eq rfl
  have h := ((S.successor 0).parameters_past 0 h0).1
  change (S.state (Nat.ceil (0 : ℝ) + 1)).parameters.delta 0 = _
  rw [Nat.ceil_zero]
  exact h

/-! ### §2 tower：accuracy 逐块缩四倍 -/

/-- tower 的每个 accuracy ≤ base block 在 `0` 处 delta 的四分之一（`_C12H`）。 -/
theorem tower_accuracy_le_base_C12H {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (n : ℕ) :
    T.accuracy n ≤ (T.block 0).parameters.delta 0 / 4 := by
  induction n with
  | zero =>
    exact BlockTower_C11W.toChain_accuracy_le_quarter T 0
  | succ n ih =>
    have h := BlockTower_C11W.toChain_accuracy_le_quarter T (n + 1)
    have hd : (T.block (n + 1)).parameters.delta (preparedSpatialHorizon (n + 1)) =
        T.accuracy n :=
      (T.extension n).successor.delta_after _ (preparedSpatialHorizon_lt_succ_C12H n)
    have hpos : 0 < T.accuracy n := (T.extension n).accuracy_pos
    change T.accuracy (n + 1) ≤ _ at h
    rw [hd] at h
    linarith

/-! ### §3 (c) 的精确判据 -/

/-- **(c) 判据（`_C12H`，PROVED）**：q 在 `[0, ∞)` 上 link 到 `chainDiagonal_C11A T.toChain`、`Λ ≥ 0` ⇒
`(∀ t ≥ 0, Λ·q.delta t ≤ 1/2) ↔ Λ·δ_{block 0}(0) ≤ 1/2`。 -/
theorem recenter_global_iff_base_C12H {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (∀ t : ℝ, 0 ≤ t → Λ * q.delta t ≤ 1 / 2) ↔ Λ * (T.block 0).parameters.delta 0 ≤ 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    rw [hq 0 le_rfl, chainDiagonal_delta_zero_C12H] at h0
    exact h0
  · intro hb t ht
    rw [hq t ht]
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, chainDiagonal_delta_zero_C12H]
      exact hb
    · obtain ⟨n, hn⟩ := chainDiagonal_delta_eq_accuracy_C12H T.toChain hpos
      rw [hn]
      have h1 : T.toChain.accuracy n ≤ (T.block 0).parameters.delta 0 / 4 :=
        tower_accuracy_le_base_C12H T n
      have hd0 : 0 < (T.block 0).parameters.delta 0 :=
        (T.block 0).parameters.delta_pos 0 le_rfl
      calc Λ * T.toChain.accuracy n ≤ Λ * (T.block 0).parameters.delta 0 :=
            mul_le_mul_of_nonneg_left (by linarith) hΛ
        _ ≤ 1 / 2 := hb

/-- **(c) 对树内 base 的反例（`_C12H`）**：`δ_{block 0}(0) = 1/2`（`PreparedSpatialBasePortC11P` 的 base
取 `δ ≡ 1/2`）、`Λ ≥ 4` ⇒ 全局 (c) 不成立。 -/
theorem not_recenter_global_of_half_C12H {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t)
    (hhalf : (T.block 0).parameters.delta 0 = 1 / 2) {Λ : ℝ} (hΛ : 4 ≤ Λ) :
    ¬ ∀ t : ℝ, 0 ≤ t → Λ * q.delta t ≤ 1 / 2 := by
  rw [recenter_global_iff_base_C12H T q hq (by linarith), hhalf]
  intro h
  linarith

/-- **`∀ q` 层 (c) 不可能（`_C12H`）**：只锁 delta / neckRadius 的 q 可以换成同 profile、
`recenterConstant` 任意大的孪生，使 (c) 在 `t = 0` 失败。 -/
theorem exists_recenter_bad_twin_C12H (q : CutoffParameters) :
    ∃ q' : CutoffParameters, q'.delta = q.delta ∧ q'.neckRadius = q.neckRadius ∧
      ¬ ∀ t : ℝ, 0 ≤ t → q'.recenterConstant * q'.delta t ≤ 1 / 2 := by
  have hd : 0 < q.delta 0 := q.delta_pos 0 le_rfl
  let q' : CutoffParameters :=
    { q with
      recenterConstant := max 4 (q.delta 0)⁻¹
      recenterConstant_ge_four := le_max_left _ _ }
  refine ⟨q', rfl, rfl, ?_⟩
  intro h
  have h0 := h 0 le_rfl
  change max 4 (q.delta 0)⁻¹ * q.delta 0 ≤ 1 / 2 at h0
  have h1 : (q.delta 0)⁻¹ * q.delta 0 ≤ max 4 (q.delta 0)⁻¹ * q.delta 0 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hd.le
  rw [inv_mul_cancel₀ hd.ne'] at h1
  linarith

/-! ### §4 (b)：观察参数的全局 link 不成立；q₀ 层 producer -/

/-- **(b) 观察参数全局形不成立（`_C12H`）**：若 `δ_diag → 0`，则不可能对一切 `n` 与 `t ≥ 0` 有
`(S.observation n).parameters.delta t = (chainDiagonal_C11A S).delta t`。 -/
theorem not_obsLink_global_C12H (S : PreparedSpatialChain pBase C P g)
    (hlim : Tendsto (chainDiagonal_C11A S).delta atTop (𝓝 0)) :
    ¬ ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      (S.observation n).parameters.delta t = (chainDiagonal_C11A S).delta t := by
  intro h
  have ha : 0 < S.accuracy 0 := S.accuracy_pos 0
  obtain ⟨t, ht⟩ := ((hlim.eventually (gt_mem_nhds ha)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hE : preparedSpatialHorizon 0 < t := by
    change (0 : ℝ) < t
    exact ht.2
  have h0 : (S.observation 0).parameters.delta t = S.accuracy 0 :=
    (S.successor 0).delta_after t hE
  rw [h 0 t ht.2.le] at h0
  linarith [ht.1]

/-- **(b) producer（`_C12H`，PROVED）**：SCRS⁺ 解包出的 `q₀`（records 的参数就是 `q₀`）在 `[0, ∞)` 上 link 到
`chainDiagonal_C11A T.toChain`，`q₀.recenterConstant = pB.recenterConstant`，`q₀.neckRadius` antitone，
`q₀.delta → 0`。 -/
theorem obsLink_of_scrsPlus_C12H {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) :
    ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters)
      (_records : CutoffRecords_C11S F₀ q₀),
      F₀.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      q₀.recenterConstant = pB.recenterConstant ∧ AntitoneOn q₀.neckRadius (Ici 0) ∧
      Tendsto q₀.delta atTop (𝓝 0) := by
  obtain ⟨F₀, q₀, -, records, ⟨hT, hdiag, hst⟩, -, -, ⟨-, hanti, hlim⟩, -⟩ := h
  exact ⟨F₀, q₀, records, hT, hdiag, hst.2.2.2.2, hanti, hlim⟩

/-- **(c) 在 q₀ 层（`_C12H`，PROVED）**：SCRS⁺ 的 `q₀` 满足全局 (c) 当且仅当
`pB.recenterConstant·δ_{block 0}(0) ≤ 1/2`。 -/
theorem recenter_q0_iff_base_C12H {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) :
    ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters)
      (_records : CutoffRecords_C11S F₀ q₀),
      (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      ((∀ t : ℝ, 0 ≤ t → q₀.recenterConstant * q₀.delta t ≤ 1 / 2) ↔
        pB.recenterConstant * (T.block 0).parameters.delta 0 ≤ 1 / 2) := by
  obtain ⟨F₀, q₀, records, -, hdiag, hΛ, -, -⟩ := obsLink_of_scrsPlus_C12H h
  refine ⟨F₀, q₀, records, hdiag, ?_⟩
  rw [hΛ]
  exact recenter_global_iff_base_C12H T q₀ (fun t ht => (hdiag t ht).1)
    (by linarith [pB.recenterConstant_ge_four])

/-! ### §5 (a) 的 diagonal 搬运 -/

/-- **(a) 搬运（`_C12H`）**：q 在 `[0, ∞)` 上 link 到 `chainDiagonal_C11A S`，diag 上的 haccuracy ⇒ q 上的
haccuracy（`2u ≥ 0`）。diag 上的 haccuracy 本身 **BLOCKED**（见文件头）。 -/
theorem hacc_of_chainDiagonal_C12H (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (hD : ∀ u : ℝ, 0 ≤ u → (chainDiagonal_C11A S).delta u ^ 2 *
      (chainDiagonal_C11A S).neckRadius u < (chainDiagonal_C11A S).neckRadius (2 * u) / (u + 1)) :
    ∀ u : ℝ, 0 ≤ u → q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1) := by
  intro u hu
  have h2u : 0 ≤ 2 * u := by linarith
  rw [(hq u hu).1, (hq u hu).2, (hq (2 * u) h2u).2]
  exact hD u hu

end GC.LongTime.Ch11
