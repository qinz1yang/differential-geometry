import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepOfSepXP6SS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryParamCompatAccP6PC

/-!
# `hstep` 的供给：θ = 2 的参数合同 ⇐ tower request 比值（O-CH11-HSCALESEP G2，后缀 `_P6SS`）

R-C11-19 Q3：chain 相邻步比 `hstep` 仍需实际供给，不能从 radius antitone 得到。树内搜索结果：
`PreparedSpatialSuccessor` 只有 `radius_le`（上界）、`accuracy_le : accuracy n ≤ 1/(n+2)`；
`LookaheadReady_C11W` 的 `rNext_le` / `threshold` / `fit` 都是 `rNext` 的**上界**；`RequestReady_C11W` 的
`cap_le_level` / `cap_le_quarter` 不含半径；`BudgetCertificate_C11GT2`（K3 / event / URE chooser 支配）也不含
半径比。**树内没有 `hstep` 的来源**（PARAMCOMPAT G4 `paramCompat_of_chain_accuracy_P6PC` 把它化成
`accuracy k · r_{k+1} ≤ r_{k+2}` + 首段 `h0`，同样无来源）。

本文件的观察：hscaleSep 链实际只用 **θ = 2**（K 窗 `Tn ≤ 2·aSeed`，`window_le_two_mul_P6PC`）。θ = 2 的窗
`x ≤ y ≤ 2x` 跨过步时 `s_j = (5/6)·3^j` 时 `x > s_j / 2 = (5/12)·3^j > 3^{j-1} = b_j`，
故 `δ(x) ≤ δ((5/12)·3^j)
= accuracy j`（`diagonal_delta_halfActivation_P6SS`），所需比值只剩**同块** `accuracy j · r_j ≤ r_{j+1}`
（无首段 `h0`）。在 tower 里 `r_{j+1} = (T.lookahead j).rNext` 由 lookahead **先**选，`accuracy j ≤
(T.request j).accuracyCap` **后**选（`BlockStep_C11W` 的量词序），所以它是一条可以在 request 选择时满足的
约束 `cap_j · r_j ≤ rNext_j`：
* `paramCompat_two_of_chain_P6SS`（PROVED 相对 `hacc`）：同块比值 ⇒ `SurgeryParamCompat_P6PC diag 2`；
* `hacc_of_requestCap_P6SS`（PROVED）：tower request 比值 `hcap` ⇒ 同块比值；
* `requestReady_capMin_P6SS` / `budgetCertificate_capMin_P6SS`（PROVED）：任一 ready / 带证书的 request 把 cap
  取 `min cap (rNext / r)` 后仍 ready、证书仍成立（`BudgetCertificate_C11GT2.mono`）——即 `hcap` 与现有
  W0 / FINEPACK 选择相容；
* `tower_of_blockSteps_ratio_P6SS`（PROVED）：与 `tower_of_blockSteps_C11W` 同前提（`∀ j BlockStep` + base），
  request 取 `ratioRequest_P6SS`，得到满足 `hcap` 的 tower；
* 槽级：`hscaleSep_slot_of_ceil_P6SS`（PROVISIONAL[`hpc`, `hceil` | S1, S14]，lead 裁定：Tn 行走 σ 处
  ceiling）、`hscaleSep_slot_of_requestCap_P6SS`（PROVISIONAL[`hcap`, `hceil` | S1, S14]）；
  比较孪生 `hscaleSep_slot_of_ceilOnly_P6SS`（INTEGRATION-ONLY：S-CH11-SCALESEP
  `hscaleSep_of_ceiling_P6SS`
  的槽形包装，PROVISIONAL[`hceil` | S1, S14]——给了 `hceil` 之后 `hpc` 不再需要）。
repair target（`hcap`）：HP6B2 槽前缀的 tower `T` 是全称的，`hcap` 不是 `BlockTower_C11W` /
`BudgetCertificate_C11GT2` / `SameConstructionRetentionSupplyPlus_C11GT6` 的字段；owner = tower 构造
（request 选择处加 `cap ≤ rNext / radius`，本文件证明可加且与证书相容）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B BlockState_C11W BlockLookahead_C11W
  BlockRequest_C11W RequestReady_C11W LookaheadReady_C11W Inv_C11W BlockStep_C11W)

/-- `(n : ℝ) ≤ (5/12)·3^n`（Bernoulli `3^m ≥ 1 + 2m`）。 -/
theorem nat_le_halfActivation_P6SS (n : ℕ) : (n : ℝ) ≤ (5 / 12 : ℝ) * 3 ^ n := by
  cases n with
  | zero => norm_num
  | succ m =>
    have hb : 1 + (m : ℝ) * 2 ≤ (1 + 2) ^ m := one_add_mul_le_pow (by norm_num) m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at hb
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

/-- **`(P6SS)` 参数合同只看 `t ≥ 0`**：`q` 与 `p` 在 `[0, ∞)` 上 `δ`、`ρ` 相等 ⇒ 合同下传。 -/
theorem paramCompat_of_eqOn_P6SS {p q : CutoffParameters} {θ : ℝ}
    (hp : SurgeryParamCompat_P6PC p θ)
    (h : ∀ t : ℝ, 0 ≤ t → q.delta t = p.delta t ∧ q.neckRadius t = p.neckRadius t) :
    SurgeryParamCompat_P6PC q θ := by
  refine ⟨fun x hx y hy hxy => ?_, fun x y hx hxy hyθ => ?_⟩
  · rw [(h x hx).2, (h y hy).2]
    exact hp.1 hx hy hxy
  · rw [(h x hx).1, (h x hx).2, (h y (hx.trans hxy)).2]
    exact hp.2 x y hx hxy hyθ

section Chain

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **diagonal `δ` 在半步时 `(5/12)·3^j` 取 `S.accuracy j`（PROVED）**：`b_j < (5/12)·3^j ≤ b_{j+1}`
（`b_0 = 0`、`b_{m+1} = 3^m`），successor `j` 的 `delta_after` + prefix compat。 -/
theorem diagonal_delta_halfActivation_P6SS (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (j : ℕ) :
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
      ((5 / 12 : ℝ) * 3 ^ j) = S.accuracy j := by
  have hp : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
  have hk := nat_le_halfActivation_P6SS j
  have hidx : j + 1 ≤ Nat.ceil ((5 / 12 : ℝ) * 3 ^ j) + 1 := by
    have h : j ≤ Nat.ceil ((5 / 12 : ℝ) * 3 ^ j) := by exact_mod_cast hk.trans (Nat.le_ceil _)
    omega
  have hle : (5 / 12 : ℝ) * 3 ^ j ≤ GC.GeneralFlow.preparedSpatialHorizon (j + 1) := by
    change (5 / 12 : ℝ) * 3 ^ j ≤ 3 ^ j
    linarith
  have hafter : GC.GeneralFlow.preparedSpatialHorizon j < (5 / 12 : ℝ) * 3 ^ j := by
    cases j with
    | zero =>
      change (0 : ℝ) < (5 / 12 : ℝ) * 3 ^ 0
      norm_num
    | succ m =>
      have hm : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) m
      change (3 : ℝ) ^ m < (5 / 12 : ℝ) * 3 ^ (m + 1)
      rw [pow_succ]
      linarith
  change (S.state (Nat.ceil ((5 / 12 : ℝ) * 3 ^ j) + 1)).parameters.delta ((5 / 12 : ℝ) * 3 ^ j) =
    S.accuracy j
  rw [state_delta_compat_P6PC S (j + 1) _ hidx _ hle]
  exact (S.successor j).delta_after _ hafter

/-- **θ = 2 的合同 ⇐ 同块比值（PROVED 相对 `hacc`）**：`accuracy j · r_j ≤ r_{j+1}`
（`r_j = (S.state j).radius`）⇒ `SurgeryParamCompat_P6PC diag 2`。跨步窗 `x ≤ s_j < y ≤ 2x` 给
`x > (5/12)·3^j`，`δ` antitone 把 `δ(x)` 压到 `accuracy j`；无首段条件。 -/
theorem paramCompat_two_of_chain_P6SS (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (hacc : ∀ j, S.accuracy j * (S.state j).radius ≤ (S.state (j + 1)).radius) :
    SurgeryParamCompat_P6PC
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)) 2 := by
  have hunb : ∀ t : ℝ, ∃ j, t ≤ (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) j := fun t =>
    ⟨Nat.ceil t, (Nat.le_ceil t).trans (nat_le_activation_P6PC _)⟩
  have hval : ∀ t, 0 ≤ t →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t =
        (S.state (stepIndex_P6PC (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) hunb t)).radius :=
    fun t ht => neckRadius_diagonal_eq_band_P6PC S _ ht
      (stepIndex_spec_P6PC (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) hunb t).1
      (stepIndex_spec_P6PC (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) hunb t).2
  have hr : Antitone (fun j => (S.state j).radius) :=
    antitone_nat_of_succ_le fun n => (S.successor n).radius_le
  have hsparse : ∀ j, 2 * (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) j ≤
      (fun j : ℕ => (5 / 6 : ℝ) * 3 ^ j) (j + 1) := fun j => by
    have hp : (0 : ℝ) ≤ 3 ^ j := by positivity
    change 2 * ((5 / 6 : ℝ) * 3 ^ j) ≤ (5 / 6 : ℝ) * 3 ^ (j + 1)
    rw [pow_succ]
    nlinarith
  refine ⟨fun x hx y hy hxy => ?_, fun x y hx hxy hy2 => ?_⟩
  · rw [hval x hx, hval y hy]
    exact hr (stepIndex_le_P6PC _ hunb (hxy.trans (stepIndex_spec_P6PC _ hunb y).1))
  · have hy0 : 0 ≤ y := hx.trans hxy
    obtain ⟨h1, h2⟩ := at_most_one_step_in_window_P6PC _ hunb (by norm_num) hsparse hxy hy2
    have hd := (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta_lt_one x hx
    have hρx :=
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius_pos x hx
    rcases Nat.eq_or_lt_of_le h2 with h3 | h3
    · have hsy := (stepIndex_spec_P6PC _ hunb y).2 (stepIndex_P6PC _ hunb x) (by omega)
      have hsy' : (5 / 6 : ℝ) * 3 ^ (stepIndex_P6PC _ hunb x) < y := hsy
      have hp : (0 : ℝ) ≤ 3 ^ (stepIndex_P6PC _ hunb x) := by positivity
      have hxh : (5 / 12 : ℝ) * 3 ^ (stepIndex_P6PC _ hunb x) ≤ x := by linarith
      have hh0 : (0 : ℝ) ≤ (5 / 12 : ℝ) * 3 ^ (stepIndex_P6PC _ hunb x) := by positivity
      have hδ := diagonal_delta_antitone_P6PC S (mem_Ici.mpr hh0) (mem_Ici.mpr hx) hxh
      rw [diagonal_delta_halfActivation_P6SS S] at hδ
      rw [hval y hy0, h3, hval x hx]
      exact (mul_le_mul_of_nonneg_right hδ (S.state _).radius_pos.le).trans (hacc _)
    · have h4 : stepIndex_P6PC _ hunb y = stepIndex_P6PC _ hunb x := by omega
      rw [hval y hy0, h4, ← hval x hx]
      nlinarith

end Chain

section Tower

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}

/-- **tower request 比值 ⇒ 同块比值（PROVED）**：`cap_j · r_j ≤ rNext_j`、`accuracy_le_cap`、
`radius_eq : r_{j+1} = rNext_j`。 -/
theorem hacc_of_requestCap_P6SS (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hcap : ∀ j, (T.request j).accuracyCap * (T.block j).radius ≤ (T.lookahead j).rNext) :
    ∀ j, T.toChain.accuracy j * (T.toChain.state j).radius ≤ (T.toChain.state (j + 1)).radius := by
  intro j
  have hd := (T.extension j).accuracy_le_cap
  have hr := (T.block j).radius_pos
  change T.accuracy j * (T.block j).radius ≤ (T.block (j + 1)).radius
  rw [(T.extension j).radius_eq]
  exact (mul_le_mul_of_nonneg_right hd hr.le).trans (hcap j)

/-- **槽前缀形（PROVED 相对 `hcap`）**：HP6B2 前缀的 `hq`（`q = chainDiagonal T.toChain` 于 `[0, ∞)`）+
`hcap` ⇒ `SurgeryParamCompat_P6PC q 2`（G1 槽定理的 `hpc`）。 -/
theorem paramCompat_q_of_requestCap_P6SS
    {T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve} {q : CutoffParameters}
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hcap : ∀ j, (T.request j).accuracyCap * (T.block j).radius ≤ (T.lookahead j).rNext) :
    SurgeryParamCompat_P6PC q 2 :=
  paramCompat_of_eqOn_P6SS
    (paramCompat_two_of_chain_P6SS T.toChain (hacc_of_requestCap_P6SS T hcap)) hq

/-- cap 取 `min cap r`（`0 < r`）后 request 仍 ready。 -/
theorem requestReady_capMin_P6SS {j : ℕ} {X : BlockState_C11W pBase C P g j}
    {req : BlockRequest_C11W} (h : RequestReady_C11W X req) {r : ℝ} (hr : 0 < r) :
    RequestReady_C11W X ⟨req.epsCut, req.Dcut, req.mcut, min req.accuracyCap r⟩ :=
  ⟨lt_min h.cap_pos hr, (min_le_left _ _).trans h.cap_le_level,
    (min_le_left _ _).trans h.cap_le_quarter, h.epsCut_pos, h.Dcut_pos⟩

/-- cap 取 `min cap r` 后 GT2 预算证书仍成立（`BudgetCertificate_C11GT2.mono`）：`hcap` 与 FINEPACK 支配
选择相容。 -/
theorem budgetCertificate_capMin_P6SS {Λrec : ℝ} {Cderiv : ℝ≥0} {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {ℓ : BlockLookahead_C11W X} {req : BlockRequest_C11W}
    (h : BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req) (r : ℝ) :
    BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ
      ⟨req.epsCut, req.Dcut, req.mcut, min req.accuracyCap r⟩ :=
  h.mono le_rfl le_rfl le_rfl (min_le_left _ _)

/-- 比值 request：W0 的 cap（`min (1/(j+2)) (δ(b_j)/4)`）再与 `rNext / radius` 取 min。 -/
def ratioRequest_P6SS {j : ℕ} (X : BlockState_C11W pBase C P g j) (ℓ : BlockLookahead_C11W X) :
    BlockRequest_C11W :=
  ⟨1, 1, 0, min (min (1 / ((j : ℝ) + 2))
    (X.parameters.delta (GC.GeneralFlow.preparedSpatialHorizon j) / 4)) (ℓ.rNext / X.radius)⟩

/-- 比值 request ready 且满足 `cap · radius ≤ rNext`（PROVED）。 -/
theorem ratioRequest_spec_P6SS {j : ℕ} (X : BlockState_C11W pBase C P g j)
    (ℓ : BlockLookahead_C11W X) (hrn : 0 < ℓ.rNext) :
    RequestReady_C11W X (ratioRequest_P6SS X ℓ) ∧
      (ratioRequest_P6SS X ℓ).accuracyCap * X.radius ≤ ℓ.rNext := by
  have hδ : 0 < X.parameters.delta (GC.GeneralFlow.preparedSpatialHorizon j) :=
    X.parameters.delta_pos _ (GC.LongTime.Ch11.blockActivation_mem_C11W j).1
  have hr := X.radius_pos
  refine ⟨⟨lt_min (lt_min (by positivity) (by positivity)) (div_pos hrn hr),
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
    one_pos, one_pos⟩, ?_⟩
  change min (min (1 / ((j : ℝ) + 2))
    (X.parameters.delta (GC.GeneralFlow.preparedSpatialHorizon j) / 4)) (ℓ.rNext / X.radius) *
      X.radius ≤ ℓ.rNext
  calc _ ≤ ℓ.rNext / X.radius * X.radius := mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
    _ = ℓ.rNext := div_mul_cancel₀ _ hr.ne'

/-- **满足 `hcap` 的 tower 存在（PROVED）**：前提与 `tower_of_blockSteps_C11W` 相同（`∀ j BlockStep` +
base `Inv_0`），request 取 `ratioRequest_P6SS`（lookahead 之后选，`BlockStep_C11W` 对**任一** ready
request 给延拓）。 -/
theorem tower_of_blockSteps_ratio_P6SS
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, T.block 0 = X₀ ∧
      ∀ j, (T.request j).accuracyCap * (T.block j).radius ≤ (T.lookahead j).rNext := by
  classical
  let Certified (n : ℕ) :=
    {X : BlockState_C11W pBase C P g n // Inv_C11W Cdist cMax Dstar εReserve X}
  let look (n : ℕ) (X : Certified n) : BlockLookahead_C11W X.1 :=
    Classical.choose (hstep n X.1 X.2)
  have look_spec (n : ℕ) (X : Certified n) :=
    Classical.choose_spec (hstep n X.1 X.2)
  let req (n : ℕ) (X : Certified n) : BlockRequest_C11W := ratioRequest_P6SS X.1 (look n X)
  have req_spec (n : ℕ) (X : Certified n) :=
    ratioRequest_spec_P6SS X.1 (look n X) (look_spec n X).1.rNext_pos
  have ext (n : ℕ) (X : Certified n) := (look_spec n X).2 (req n X) (req_spec n X).1
  let next (n : ℕ) (X : Certified n) : Certified (n + 1) :=
    ⟨Classical.choose (ext n X), (Classical.choose_spec (Classical.choose_spec (ext n X))).2⟩
  let acc (n : ℕ) (X : Certified n) : ℝ := Classical.choose (Classical.choose_spec (ext n X))
  have next_spec (n : ℕ) (X : Certified n) :
      GC.LongTime.Ch11.PhysicalExtension_C11W X.1 (next n X).1 (look n X) (req n X) (acc n X) :=
    (Classical.choose_spec (Classical.choose_spec (ext n X))).1
  let chain : ∀ n : ℕ, Certified n := fun n => Nat.rec ⟨X₀, hX₀⟩ (fun n X => next n X) n
  exact ⟨{ block := fun n => (chain n).1
           lookahead := fun n => look n (chain n)
           request := fun n => req n (chain n)
           accuracy := fun n => acc n (chain n)
           inv := fun n => (chain n).2
           ready := fun n => ⟨(look_spec n (chain n)).1, (req_spec n (chain n)).1⟩
           extension := fun n => next_spec n (chain n)
           initial_history := hhist
           initial_radius_le := hrad }, rfl, fun n => (req_spec n (chain n)).2⟩

end Tower

/-- **槽体，σ 处 ceiling 版（PROVISIONAL[`hpc`, `hceil` | S1, S14]）**：G1 槽体的 `hTn` 由 `hceil`
（S-CH11-SCALESEP `hscaleSep_of_ceiling_P6SS` 的同名 binder，逐字形）+ 合同的 antitone 经
`tnRow_of_sigmaCeil_P6SS` 付（lead 裁定：Tn 行走 σ 处 ceiling，不改冻结槽形）。 -/
theorem hscaleSep_body_of_ceil_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hpc : SurgeryParamCompat_P6PC q 2)
    (hceil :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
  hscaleSep_body_of_paramCompat_P6SS hS14 hδq hpc (by
    intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
      hRr hL hsel hgood hwin hwin' hroom hradii i hi k
    exact tnRow_of_sigmaCeil_P6SS (paramCompat_rescale_P6PC hpc (c k) (hc k)) (σ k).2.1 (hsT k)
      (hceil ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
        hRr hL hsel hgood hwin hwin' hroom hradii i hi k))

/-- **HP6B2 `hscaleSep` 槽，ceiling 版（PROVISIONAL[`hpc`, `hceil` | S1 `hδq`, S14 `hS14`]）**：结论 =
`P6HP6bAssemblyV2P6HPB2.lean:1490–1543` 逐字。 -/
theorem hscaleSep_slot_of_ceil_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hS14 :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      Tendsto q.delta atTop (𝓝 0))
    (hpc :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      SurgeryParamCompat_P6PC q 2)
    (hceil :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  exact hscaleSep_body_of_ceil_P6SS
    (hS14 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hδq hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hpc hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hceil hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt)

/-- **HP6B2 `hscaleSep` 槽，`hpc` ⇐ tower request 比值（PROVISIONAL[`hcap`, `hceil` | S1, S14]）**：
`hpc` 由 `paramCompat_q_of_requestCap_P6SS`（前缀的 `hq` + `hcap`）付。 -/
theorem hscaleSep_slot_of_requestCap_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hS14 :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      Tendsto q.delta atTop (𝓝 0))
    (hcap :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ j, (T.request j).accuracyCap * (T.block j).radius ≤ (T.lookahead j).rNext)
    (hceil :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  refine hscaleSep_slot_of_ceil_P6SS εP6 hS14 hδq ?_ hceil
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord
  exact paramCompat_q_of_requestCap_P6SS hq
    (hcap hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)

/-- **比较孪生（INTEGRATION-ONLY，PROVISIONAL[`hceil` | S1, S14]）**：S-CH11-SCALESEP
`hscaleSep_of_ceiling_P6SS`（records ⇐ S14 经 `lateRecords_of_S14_P6SS` /
`hrec_of_lateRecords_P6SS`）的槽形包装。给了 `hceil` 后 hsepX 路线的 `hpc` 不再需要。 -/
theorem hscaleSep_slot_of_ceilOnly_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hS14 :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      Tendsto q.delta atTop (𝓝 0))
    (hceil :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  exact ObservedHistory.hscaleSep_of_ceiling_P6SS
    (hδq hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (ObservedHistory.hrec_of_lateRecords_P6SS (ObservedHistory.lateRecords_of_S14_P6SS
      (hS14 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)))
    (hceil hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt)

/-- **consumer（G2）**：ceiling 版 / request 比值版 / 比较孪生三个槽产出都经 named argument 喂进
`hP6bTwoLevelTime_of_slots_v2_P6HPB2`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 hδq hcap hceil =>
  ObservedHistory.hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6
    (hscaleSep := hscaleSep_slot_of_requestCap_P6SS (P := P) (g := g) εP6 hS14 hδq hcap hceil)

example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 hδq hpc hceil =>
  ObservedHistory.hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6
    (hscaleSep := hscaleSep_slot_of_ceil_P6SS (P := P) (g := g) εP6 hS14 hδq hpc hceil)

example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 hδq hceil =>
  ObservedHistory.hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6
    (hscaleSep := hscaleSep_slot_of_ceilOnly_P6SS (P := P) (g := g) εP6 hS14 hδq hceil)

/-- consumer：`ratioRequest_P6SS` tower 的链参数满足 θ = 2 合同（存在性 + 合同，一条链走通）。 -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2 := by
  obtain ⟨T, -, hcap⟩ := tower_of_blockSteps_ratio_P6SS hstep X₀ hX₀ hhist hrad
  exact ⟨T, paramCompat_two_of_chain_P6SS T.toChain (hacc_of_requestCap_P6SS T hcap)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
