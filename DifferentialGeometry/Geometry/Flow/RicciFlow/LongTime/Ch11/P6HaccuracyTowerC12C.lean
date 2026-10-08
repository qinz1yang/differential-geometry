import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ProfileClausesC12H
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopBudgetC11GT2

set_option autoImplicit false

/-!
# C12-7′c：tower 请求 cap 的 min 孪生 ⇒ SCRS⁺ 的 `q₀` 满足 haccuracy（后缀 `_C12C`）

**G0（不循环）**：`BlockStep_C11W` 的量词序是 `∃ ℓ, LookaheadReady ∧ ∀ req, RequestReady → ∃ Y d, …`，
`ℓ.rNext = Y.radius = r_{j+1}`（`radius_eq`）在 request 之前选、与 request 无关；`accuracy j ≤ cap_j`
（`accuracy_le_cap`）。所以块 `j` 的 cap 可以依赖 `r_{j+1}`，没有回路
（`tower_of_blockSteps_policy_C11Q6` 正是先 look 再 req）。

**时间骨架**：`b_0 = 0`、`b_{j+1} = 3^j`、块 `j+1` 的半径在 `(5/6)·3^j` 之后生效。`u ∈ (b_j, b_{j+1}]` 时
`δ_diag(u) = accuracy j`、`ρ_diag(u) ≤ r_j`、`ρ_diag(2u) ≥ r_{j+1}`（`2u ≤ 2·3^j ≤ (5/6)·3^{j+1}`）、
`u + 1 ≤ 3^j + 1`；`accuracy < 1` ⇒ `a² < a`，所以条款
`cap_j · r_j · (3^j + 1) ≤ r_{j+1}`（不开方）就给出 `δ(u)²ρ(u) < ρ(2u)/(u+1)`；`u = 0` 由 `δ(0) < 1`。

* `chainDiagonal_haccuracy_C12C`：chain 条款 ⇒ diag 上 haccuracy（PROVED）。
* `exists_budget_tower_scaled_C12C`：`exists_budget_tower_C11GT2` 的孪生（同前提），cap 再取
  `min · (rNext / (r_j·(3^j+1)))`；证书（`.mono`）、共尾、`cap ≤ δ₀`、ready 全保持（PROVED）。
* **`haccuracy_of_scrsPlus_C12H`**（裁定原名）：满足 cap 条款的 `T` 上，SCRS⁺ 解包的 `q₀` 满足 haccuracy。
* `exists_tower_q0_haccuracy_C12C`：孪生 builder + SCRS⁺ producer
  `sameConstructionRetentionSupplyPlus_of_tower_C11GT6` 端到端。

**与冻结槽的关系**：冻结 ch8 槽对 `∀ T`（带证书 ∧ 共尾）全称，不带 cap 条款；孪生 builder 产出的 `T`
满足槽的全部前提，所以是槽的合法实例；但槽体内部拿不到 haccuracy——要在槽内用，需要槽带 cap 条款
（或 ch8 把 C12-7′c 作显式 profile 前提），本文件不改槽。
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

/-! ### §1 时间骨架与 chain 前缀相容 -/

/-- `b_n` 单调（`_C12C`）。 -/
theorem preparedSpatialHorizon_mono_C12C : Monotone preparedSpatialHorizon :=
  monotone_nat_of_le_succ fun n => (preparedSpatialHorizon_lt_succ_C12H n).le

/-- `t ≤ b_{⌈t⌉+1}`（`_C12C`）。 -/
theorem le_preparedSpatialHorizon_ceil_C12C (t : ℝ) :
    t ≤ preparedSpatialHorizon (Nat.ceil t + 1) := by
  change t ≤ (3 : ℝ) ^ (Nat.ceil t)
  exact (Nat.le_ceil t).trans (nat_lt_three_pow _).le

/-- `0 < u` ⇒ 存在块 `j` 使 `b_j < u ≤ b_{j+1}`（`_C12C`）。 -/
theorem exists_block_C12C {u : ℝ} (hu : 0 < u) :
    ∃ j : ℕ, preparedSpatialHorizon j < u ∧ u ≤ preparedSpatialHorizon (j + 1) := by
  classical
  have hex : ∃ j : ℕ, u ≤ preparedSpatialHorizon (j + 1) :=
    ⟨Nat.ceil u, le_preparedSpatialHorizon_ceil_C12C u⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_cases h0 : Nat.find hex = 0
  · rw [h0]
    change (0 : ℝ) < u
    exact hu
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [hk]
    exact lt_of_not_ge hmin

/-- 前缀相容：`t ≤ b_M` ⇒ `state (M+k)` 与 `state M` 在 `t` 处 delta / neckRadius 相同（`_C12C`）。 -/
theorem chainState_compat_C12C (S : PreparedSpatialChain pBase C P g) {M : ℕ} {t : ℝ}
    (ht : t ≤ preparedSpatialHorizon M) (k : ℕ) :
    (S.state (M + k)).parameters.delta t = (S.state M).parameters.delta t ∧
      (S.state (M + k)).parameters.neckRadius t = (S.state M).parameters.neckRadius t := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hle : t ≤ preparedSpatialHorizon (M + k) :=
      ht.trans (preparedSpatialHorizon_mono_C12C (Nat.le_add_right M k))
    have hp := (S.successor (M + k)).parameters_past t hle
    exact ⟨hp.1.trans ih.1, hp.2.1.trans ih.2⟩

/-- diag 在 `t ≤ b_M` 处等于 `state M`（`_C12C`）。 -/
theorem chainDiagonal_eq_state_C12C (S : PreparedSpatialChain pBase C P g) {M : ℕ} {t : ℝ}
    (ht : t ≤ preparedSpatialHorizon M) :
    (chainDiagonal_C11A S).delta t = (S.state M).parameters.delta t ∧
      (chainDiagonal_C11A S).neckRadius t = (S.state M).parameters.neckRadius t := by
  change (S.state (Nat.ceil t + 1)).parameters.delta t = _ ∧
    (S.state (Nat.ceil t + 1)).parameters.neckRadius t = _
  rcases le_total (Nat.ceil t + 1) M with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hc := chainState_compat_C12C S (le_preparedSpatialHorizon_ceil_C12C t) k
    exact ⟨hc.1.symm, hc.2.symm⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    exact chainState_compat_C12C S ht k

/-! ### §2 块内读出与 haccuracy -/

/-- 块 `j` 内（`b_j < u ≤ b_{j+1}`）：`δ(u) = accuracy j`、`ρ(u) ≤ r_j`、`r_{j+1} ≤ ρ(2u)`（`_C12C`）。 -/
theorem chainDiagonal_block_C12C (S : PreparedSpatialChain pBase C P g) (j : ℕ) {u : ℝ}
    (hlo : preparedSpatialHorizon j < u) (hhi : u ≤ preparedSpatialHorizon (j + 1)) :
    (chainDiagonal_C11A S).delta u = S.accuracy j ∧
      (chainDiagonal_C11A S).neckRadius u ≤ (S.state j).radius ∧
      (S.state (j + 1)).radius ≤ (chainDiagonal_C11A S).neckRadius (2 * u) := by
  have hu3 : u ≤ (3 : ℝ) ^ j := hhi
  have h3 : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
  have hu0 : 0 ≤ u := (blockActivation_mem_C11W j).1.trans hlo.le
  obtain ⟨hδ, hρ⟩ := chainDiagonal_eq_state_C12C S hhi
  have h2u : 2 * u ≤ preparedSpatialHorizon (j + 2) := by
    change 2 * u ≤ (3 : ℝ) ^ (j + 1)
    rw [pow_succ]
    linarith
  obtain ⟨-, hρ2⟩ := chainDiagonal_eq_state_C12C S h2u
  refine ⟨hδ.trans ((S.successor j).delta_after u hlo), ?_, ?_⟩
  · rw [hρ]
    by_cases ha : (5 / 6 : ℝ) * 3 ^ j < u
    · rw [(S.successor j).radius_after_activation u ha]
      exact (S.successor j).radius_le
    · rw [(S.successor j).radius_before_activation u (not_lt.mp ha),
        (S.state j).radius_after u hlo.le]
  · rw [hρ2]
    have hact : 2 * u ≤ (5 / 6 : ℝ) * 3 ^ (j + 1) := by
      rw [pow_succ]
      linarith
    rw [(S.successor (j + 1)).radius_before_activation (2 * u) hact]
    have hE : (0 : ℝ) ≤ preparedSpatialHorizon (j + 1) := (blockActivation_mem_C11W (j + 1)).1
    have hm : 2 * u ≤ max (2 * u) (preparedSpatialHorizon (j + 1)) := le_max_left _ _
    have hanti := (S.state (j + 1)).radius_antitone (mem_Ici.mpr (by linarith))
      (mem_Ici.mpr (hE.trans (le_max_right _ _))) hm
    rw [(S.state (j + 1)).radius_after _ (le_max_right _ _)] at hanti
    exact hanti

/-- **chain 条款 ⇒ diag haccuracy（`_C12C`，PROVED）**：
`∀ j, accuracy j · r_j · (3^j + 1) ≤ r_{j+1}` ⇒ `∀ u ≥ 0, δ(u)²ρ(u) < ρ(2u)/(u+1)`。 -/
theorem chainDiagonal_haccuracy_C12C (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ j : ℕ, S.accuracy j * (S.state j).radius * ((3 : ℝ) ^ j + 1) ≤
      (S.state (j + 1)).radius) :
    ∀ u : ℝ, 0 ≤ u → (chainDiagonal_C11A S).delta u ^ 2 * (chainDiagonal_C11A S).neckRadius u <
      (chainDiagonal_C11A S).neckRadius (2 * u) / (u + 1) := by
  intro u hu
  rcases hu.eq_or_lt with h0 | hpos
  · rw [← h0]
    have hd := (chainDiagonal_C11A S).delta_pos 0 le_rfl
    have hd1 := (chainDiagonal_C11A S).delta_lt_one 0 le_rfl
    have hρ := (chainDiagonal_C11A S).neckRadius_pos 0 le_rfl
    rw [mul_zero, zero_add, div_one]
    have hsq : (chainDiagonal_C11A S).delta 0 ^ 2 < 1 := by nlinarith
    nlinarith
  · obtain ⟨j, hlo, hhi⟩ := exists_block_C12C hpos
    obtain ⟨hδ, hρu, hρ2⟩ := chainDiagonal_block_C12C S j hlo hhi
    have ha := S.accuracy_pos j
    have ha1 := S.accuracy_lt_one j
    have hrj := (S.state j).radius_pos
    have hρpos := (chainDiagonal_C11A S).neckRadius_pos u hu
    have hu3 : u ≤ (3 : ℝ) ^ j := hhi
    have h3 : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
    have hX : 0 < (S.state j).radius * ((3 : ℝ) ^ j + 1) := by positivity
    have h2 : S.accuracy j ^ 2 < S.accuracy j := by nlinarith
    rw [hδ, lt_div_iff₀ (by linarith)]
    calc S.accuracy j ^ 2 * (chainDiagonal_C11A S).neckRadius u * (u + 1)
        ≤ S.accuracy j ^ 2 * (S.state j).radius * ((3 : ℝ) ^ j + 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hρu (sq_nonneg _)) (by linarith)
            (by linarith) (by positivity)
      _ < S.accuracy j * (S.state j).radius * ((3 : ℝ) ^ j + 1) := by
          have := mul_lt_mul_of_pos_right h2 hX
          linarith
      _ ≤ (S.state (j + 1)).radius := hS j
      _ ≤ (chainDiagonal_C11A S).neckRadius (2 * u) := hρ2

/-! ### §3 tower：cap 条款与孪生 builder -/

/-- tower cap 条款 ⇒ chain 条款（`accuracy_le_cap`、`radius_eq`）（`_C12C`）。 -/
theorem chain_scale_of_tower_C12C {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hcap : ∀ j : ℕ, (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
      (T.lookahead j).rNext) :
    ∀ j : ℕ, T.toChain.accuracy j * (T.toChain.state j).radius * ((3 : ℝ) ^ j + 1) ≤
      (T.toChain.state (j + 1)).radius := by
  intro j
  have hd := (T.extension j).accuracy_le_cap
  have hr := (T.block j).radius_pos
  have hc : (0 : ℝ) < (3 : ℝ) ^ j + 1 := by positivity
  change T.accuracy j * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤ (T.block (j + 1)).radius
  rw [(T.extension j).radius_eq]
  calc T.accuracy j * (T.block j).radius * ((3 : ℝ) ^ j + 1)
      ≤ (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) := by gcongr
    _ ≤ _ := hcap j

/-- 孪生请求：cap 再取 `min · (rNext / (r_j·(3^j+1)))`，其余字段不动（`_C12C`）。 -/
def scaledRequest_C12C {j : ℕ} (X : BlockState_C11W pBase C P g j) (ℓ : BlockLookahead_C11W X)
    (req : BlockRequest_C11W) : BlockRequest_C11W :=
  ⟨req.epsCut, req.Dcut, req.mcut,
    min req.accuracyCap (ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1)))⟩

/-- **孪生预算 tower（`_C12C`，PROVED）**：前提与 `exists_budget_tower_C11GT2` 逐字相同；产出的 tower 每块
带证书 ∧ 共尾 ∧ `cap ≤ δ₀`，且满足 cap 条款。 -/
theorem exists_budget_tower_scaled_C12C {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} {Λrec : ℝ}
    (hΛ : 0 < Λrec) (Cderiv : ℝ≥0) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, T.block 0 = X₀ ∧ ∀ j,
      (BudgetCertificate_C11GT2 Λrec Cderiv j (T.block j) (T.lookahead j) (T.request j) ∧
        RequestCofinal_C11W4 j (T.request j) ∧ (T.request j).accuracyCap ≤ δ₀) ∧
      (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
        (T.lookahead j).rNext := by
  refine tower_of_blockSteps_policy_C11Q6
    (fun j X ℓ req => (BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req ∧
      RequestCofinal_C11W4 j req ∧ req.accuracyCap ≤ δ₀) ∧
      req.accuracyCap * X.radius * ((3 : ℝ) ^ j + 1) ≤ ℓ.rNext)
    (fun j X _ ℓ hℓ => ?_) hstep X₀ hX₀ hhist hrad
  obtain ⟨req, hready, hcert, hcof, hδ⟩ :=
    budgetChoice_certified_C11GT2 hΛ Cderiv δ₀ hδ₀ j X hℓ.rNext_pos
  have hr := X.radius_pos
  have hc : (0 : ℝ) < X.radius * ((3 : ℝ) ^ j + 1) := by positivity
  have hs : 0 < ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1)) := div_pos hℓ.rNext_pos hc
  refine ⟨scaledRequest_C12C X ℓ req, ⟨lt_min hready.cap_pos hs,
    (min_le_left _ _).trans hready.cap_le_level, (min_le_left _ _).trans hready.cap_le_quarter,
    hready.epsCut_pos, hready.Dcut_pos⟩,
    ⟨hcert.mono le_rfl le_rfl le_rfl (min_le_left _ _), hcof, (min_le_left _ _).trans hδ⟩, ?_⟩
  change min req.accuracyCap (ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1))) * X.radius *
    ((3 : ℝ) ^ j + 1) ≤ ℓ.rNext
  calc min req.accuracyCap (ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1))) * X.radius *
        ((3 : ℝ) ^ j + 1)
      = min req.accuracyCap (ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1))) *
          (X.radius * ((3 : ℝ) ^ j + 1)) := by ring
    _ ≤ ℓ.rNext / (X.radius * ((3 : ℝ) ^ j + 1)) * (X.radius * ((3 : ℝ) ^ j + 1)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hc.le
    _ = ℓ.rNext := div_mul_cancel₀ _ hc.ne'

/-! ### §4 交付：SCRS⁺ 的 `q₀` 上的 haccuracy -/

/-- **`haccuracy_of_scrsPlus_C12H`（PROVED）**：tower `T` 满足 cap 条款（孪生 builder 产出）时，SCRS⁺ 解包的
`q₀`（records 的参数）在 `[0, ∞)` 上 link 到 diag，且 `∀ u ≥ 0, δ(u)²ρ(u) < ρ(2u)/(u+1)`。 -/
theorem haccuracy_of_scrsPlus_C12H {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hcap : ∀ j : ℕ, (T.request j).accuracyCap * (T.block j).radius * ((3 : ℝ) ^ j + 1) ≤
      (T.lookahead j).rNext)
    (h : SameConstructionRetentionSupplyPlus_C11GT6 T) :
    ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters)
      (_records : CutoffRecords_C11S F₀ q₀),
      F₀.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      q₀.recenterConstant = pB.recenterConstant ∧ AntitoneOn q₀.neckRadius (Ici 0) ∧
      Tendsto q₀.delta atTop (𝓝 0) ∧
      ∀ u : ℝ, 0 ≤ u → q₀.delta u ^ 2 * q₀.neckRadius u < q₀.neckRadius (2 * u) / (u + 1) := by
  obtain ⟨F₀, q₀, records, hT, hdiag, hΛ, hanti, hlim⟩ := obsLink_of_scrsPlus_C12H h
  exact ⟨F₀, q₀, records, hT, hdiag, hΛ, hanti, hlim,
    hacc_of_chainDiagonal_C12H T.toChain q₀ hdiag
      (chainDiagonal_haccuracy_C12C T.toChain (chain_scale_of_tower_C12C T hcap))⟩

/-- **端到端（`_C12C`，PROVED）**：孪生 builder + SCRS⁺ producer。前提 = `exists_budget_tower_C11GT2` 的
前提（`Λrec := pB.recenterConstant`、`Cderiv := Γ.Ctime`、冻结槽的 `cMax = 1`、`Dstar = R+1`）+ producer 的
model 条件；结论：带证书 ∧ 共尾的 tower 及其 SCRS⁺ `q₀` 上的 haccuracy。 -/
theorem exists_tower_q0_haccuracy_C12C (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εS : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εS Γ) ∧
    ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve δ₀ : ℝ),
      0 < δ₀ →
      (∀ j, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j) →
      ∀ X₀ : BlockState_C11W pB Γ P g 0,
      Inv_C11W Cdist 1 (capWindowRadius_C11E + 1) εReserve X₀ →
      X₀.history = RetainedCoreHistory.atZero P g → X₀.radius ≤ 1 →
      pB.modelAccuracy ≤ εS Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∃ T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve,
        (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
          (T.lookahead j) (T.request j) ∧ RequestCofinal_C11W4 j (T.request j)) ∧
        SameConstructionRetentionSupplyPlus_C11GT6 T ∧
        ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters)
          (_records : CutoffRecords_C11S F₀ q₀),
          F₀.tower = T.toChain.tower ∧
          (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
            q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
          ∀ u : ℝ, 0 ≤ u →
            q₀.delta u ^ 2 * q₀.neckRadius u < q₀.neckRadius (2 * u) / (u + 1) := by
  obtain ⟨εS, hεS, hprod⟩ := sameConstructionRetentionSupplyPlus_of_tower_C11GT6 P g
  refine ⟨εS, hεS, ?_⟩
  intro pB Γ Cdist εReserve δ₀ hδ₀ hstep X₀ hX₀ hhist hrad hacc hrB hoB
  have hΛ : 0 < pB.recenterConstant := by linarith [pB.recenterConstant_ge_four]
  obtain ⟨T, -, hT⟩ := exists_budget_tower_scaled_C12C hΛ Γ.Ctime δ₀ hδ₀ hstep X₀ hX₀ hhist hrad
  have hQ : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j) ∧ RequestCofinal_C11W4 j (T.request j) :=
    fun j => ⟨(hT j).1.1, (hT j).1.2.1⟩
  have hS := hprod Cdist εReserve T hQ hacc hrB hoB
  obtain ⟨F₀, q₀, records, hTw, hdiag, -, -, -, hacc'⟩ :=
    haccuracy_of_scrsPlus_C12H (fun j => (hT j).2) hS
  exact ⟨T, hQ, hS, F₀, q₀, records, hTw, hdiag, hacc'⟩

end GC.LongTime.Ch11
