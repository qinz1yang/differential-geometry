import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepConsumerC11W

set_option autoImplicit false

/-!
# S-CH11-W1L4 (G2)：W+ 请求共尾合同 `RequestCofinal_C11W4` 与 `d_j` 正下界（`_C11W4`，rev2 §5.1）

外审 R-C11-3 D-11：`RequestReady_C11W` 只要求 `εcut > 0`、`Dcut > 0`、`mcut ∈ ℕ`，推不出请求共尾。
W+ 在每块再加：
* `RequestCofinal_C11W4 j req`：`req.epsCut ≤ 1/(j+2)`、`j + 1 ≤ req.Dcut`、`j ≤ req.mcut`；
* `budgetChoice_cofinal_C11W4`：W0 的平凡加强（`εcut = 1/(j+2)`、`Dcut = j+1`、`mcut = j`、
  `cap = min (1/(j+2)) (δ(b_j)/4)`），仍是定理，不进 narrow A12；
* `requestCofinal_eventually_C11W4`：任意固定请求 `(ε, D, m)`（`ε > 0`）对 `j` 充分大都被
  `RequestCofinal` 的请求满足；
* `fine_request_of_cofinal_C11W4` / `tower_fine_request_eventually_C11W4`：经
  `retention.fine_accuracy` / `fine_radius` / `fine_order`，`BlockTower` 第 `j` 步 retention 的 fine
  参数最终满足固定请求；
  `tower_accuracy_eventually_le_C11W4`：链精度 `d_j ≤ 1/(j+2) ≤ ε` 最终成立；
* `d_j` 正下界（`d_j ≤ cap_j` 只给上界）：每个 state 有 `delta_antitone` 与 `delta_pos`，故 `[0, T]` 上
  `δ ≥ δ(T) > 0`（`state_delta_lower_bound_C11W4`）；`successor.delta_after` 给 `δ_{j+1}(t) = d_j`
  （`t > b_j`），故 `d_j` 恰是第 `j+1` 块 schedule 在 `[0, b_{j+1}]` 上的下确界
  （`accuracy_le_delta_on_block_C11W4`）；有限多块的 `d_j` 取有限 min（`exists_pos_lower_bound_finite_C11W4`）；
  对角 `chainDiagonal_C11A` 的同一结论由 `AntitoneOn q.delta (Ici 0)`
  （`w1_of_preparedSpatialChain_C11A` 的输出）给出（`chainDiagonal_delta_lower_bound_C11W4`）。
* consumer：`BlockTower` + 逐块 `RequestCofinal` ⇒ 固定请求最终被 retention 的 fine 参数满足。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **W+ 请求共尾（D-11）**：第 `j` 块的 fine request 满足 `epsCut ≤ 1/(j+2)`、`j + 1 ≤ Dcut`、
`j ≤ mcut`。 -/
def RequestCofinal_C11W4 (j : ℕ) (req : BlockRequest_C11W) : Prop :=
  req.epsCut ≤ 1 / ((j : ℝ) + 2) ∧ (j : ℝ) + 1 ≤ req.Dcut ∧ j ≤ req.mcut

/-- `RequestCofinal_C11W4` 的 inhabitant：`⟨1/(j+2), j+1, j, cap⟩`。 -/
def BlockRequest_C11W.cofinal (j : ℕ) (cap : ℝ) : BlockRequest_C11W :=
  ⟨1 / ((j : ℝ) + 2), (j : ℝ) + 1, j, cap⟩

theorem requestCofinal_cofinal_C11W4 (j : ℕ) (cap : ℝ) :
    RequestCofinal_C11W4 j (BlockRequest_C11W.cofinal j cap) :=
  ⟨le_rfl, le_rfl, le_rfl⟩

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **W0 的共尾加强（仍是定理）**：`εcut = 1/(j+2)`、`Dcut = j+1`、`mcut = j`、
`cap = min (1/(j+2)) (δ(b_j)/4)`。 -/
theorem budgetChoice_cofinal_C11W4 (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (j : ℕ) :
    ∀ X : BlockState_C11W pBase C P g j, Inv_C11W Cdist cMax Dstar εReserve X →
      ∀ ℓ : BlockLookahead_C11W X, LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ →
        ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧ RequestCofinal_C11W4 j req := by
  intro X _ _ _
  have hδ : 0 < X.parameters.delta (preparedSpatialHorizon j) :=
    X.parameters.delta_pos _ (blockActivation_mem_C11W j).1
  have hj2 : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
  refine ⟨BlockRequest_C11W.cofinal j
    (min (1 / ((j : ℝ) + 2)) (X.parameters.delta (preparedSpatialHorizon j) / 4)), ?_,
    requestCofinal_cofinal_C11W4 _ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 0 < min (1 / ((j : ℝ) + 2)) (X.parameters.delta (preparedSpatialHorizon j) / 4)
    exact lt_min hj2 (by positivity)
  · exact min_le_left _ _
  · exact min_le_right _ _
  · exact hj2
  · change 0 < (j : ℝ) + 1
    positivity

/-- **固定请求最终被满足**：`ε > 0`，`D` 任意，`m` 任意；`j` 充分大时，任何满足 `RequestCofinal_C11W4 j` 的
请求都有 `epsCut ≤ ε`、`D ≤ Dcut`、`m ≤ mcut`（阈值 `max ⌈1/ε⌉ ⌈D⌉ m`）。 -/
theorem requestCofinal_eventually_C11W4 {ε : ℝ} (hε : 0 < ε) (D : ℝ) (m : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ req : BlockRequest_C11W, RequestCofinal_C11W4 j req →
      req.epsCut ≤ ε ∧ D ≤ req.Dcut ∧ m ≤ req.mcut := by
  refine eventually_atTop.2 ⟨max (max ⌈1 / ε⌉₊ ⌈D⌉₊) m, fun j hj req hreq => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hreq
  have hj1 : ⌈1 / ε⌉₊ ≤ j := (le_max_left _ _).trans ((le_max_left _ _).trans hj)
  have hj2 : ⌈D⌉₊ ≤ j := (le_max_right _ _).trans ((le_max_left _ _).trans hj)
  have hj3 : m ≤ j := (le_max_right _ _).trans hj
  refine ⟨h1.trans ?_, ?_, hj3.trans h3⟩
  · have hjR : 1 / ε ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hj1)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hjR
    nlinarith
  · have hjR : D ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hj2)
    linarith

/-- **retention 的 fine 参数**：`retention.fine_accuracy / fine_radius / fine_order` 把请求界搬到
`W.fineParameters`：共尾请求给出 `modelAccuracy ≤ 1/(j+2)`、`j + 1 ≤ modelRadius`、`j ≤ modelOrder`。 -/
theorem fine_request_of_cofinal_C11W4 {j : ℕ} {X : BlockState_C11W pBase C P g j}
    {Y : BlockState_C11W pBase C P g (j + 1)} {d eta : ℝ} {req : BlockRequest_C11W}
    (hcof : RequestCofinal_C11W4 j req)
    (W : PreparedSpatialStepRetention X Y d eta req.epsCut req.Dcut req.mcut) :
    W.fineParameters.modelAccuracy ≤ 1 / ((j : ℝ) + 2) ∧
      (j : ℝ) + 1 ≤ W.fineParameters.modelRadius ∧ j ≤ W.fineParameters.modelOrder :=
  ⟨W.fine_accuracy.trans hcof.1, hcof.2.1.trans W.fine_radius, hcof.2.2.trans W.fine_order⟩

variable {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}

/-- **BlockTower 的预算序列满足 RequestCofinal ⇒ 任意固定请求最终满足**：第 `j` 步 retention 的
fine 参数（所有 witness）`modelAccuracy ≤ ε`、`D ≤ modelRadius`、`m ≤ modelOrder` 对 `j` 充分大成立。 -/
theorem tower_fine_request_eventually_C11W4
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hcof : ∀ j, RequestCofinal_C11W4 j (T.request j)) {ε : ℝ} (hε : 0 < ε) (D : ℝ) (m : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ W : PreparedSpatialStepRetention (T.block j) (T.block (j + 1))
        (T.accuracy j) (1 / ((j : ℝ) + 2)) (T.request j).epsCut (T.request j).Dcut
        (T.request j).mcut,
      W.fineParameters.modelAccuracy ≤ ε ∧ D ≤ W.fineParameters.modelRadius ∧
        m ≤ W.fineParameters.modelOrder := by
  filter_upwards [requestCofinal_eventually_C11W4 hε D m] with j hj W
  obtain ⟨h1, h2, h3⟩ := hj (T.request j) (hcof j)
  exact ⟨W.fine_accuracy.trans h1, h2.trans W.fine_radius, h3.trans W.fine_order⟩

/-- 链精度也最终满足：`d_j ≤ cap_j ≤ 1/(j+2) ≤ ε`（对任意 `BlockTower`，不需要共尾）。 -/
theorem tower_accuracy_eventually_le_C11W4
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, T.accuracy j ≤ ε := by
  have h : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 2) ≤ ε := by
    refine eventually_atTop.2 ⟨⌈1 / ε⌉₊, fun j hj => ?_⟩
    have hjR : 1 / ε ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hj)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hjR
    nlinarith
  filter_upwards [h] with j hj
  exact (T.toChain.accuracy_le j).trans hj

/-! ## `d_j` 正下界 -/

/-- 反单调 + 正 ⇒ `[0, T]` 上有正下界 `δ(T)`（对角 `q` 与任意 state 的 `parameters` 共用）。 -/
theorem delta_lower_bound_of_antitone_C11W4 (q : CutoffParameters)
    (hanti : AntitoneOn q.delta (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    0 < q.delta T ∧ ∀ t ∈ Icc (0 : ℝ) T, q.delta T ≤ q.delta t :=
  ⟨q.delta_pos T hT, fun _ ht => hanti ht.1 hT ht.2⟩

/-- state 版：每个 `BlockState_C11W` 的 `parameters.delta` 在 `[0, T]` 上 `≥ δ(T) > 0`。 -/
theorem state_delta_lower_bound_C11W4 {j : ℕ} (X : BlockState_C11W pBase C P g j) {T : ℝ}
    (hT : 0 ≤ T) :
    0 < X.parameters.delta T ∧ ∀ t ∈ Icc (0 : ℝ) T, X.parameters.delta T ≤ X.parameters.delta t :=
  delta_lower_bound_of_antitone_C11W4 X.parameters X.delta_antitone hT

/-- 冻结骨架：`b_j < b_{j+1}`（`0 < 1 = 3^0`，`3^{j-1} < 3^j`）。 -/
theorem preparedSpatialHorizon_lt_succ_C11W4 (j : ℕ) :
    preparedSpatialHorizon j < preparedSpatialHorizon (j + 1) := by
  cases j with
  | zero => norm_num [preparedSpatialHorizon]
  | succ n =>
    change (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 1)
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n)

/-- **`d_j` 是第 `j+1` 块 schedule 的实际下确界**：`successor.delta_after` 给
`δ_{j+1}(t) = d_j`（`t > b_j`），`δ_{j+1}` 反单调，所以 `[0, b_{j+1}]` 上 `δ_{j+1} ≥ d_j`；
`d_j > 0` 来自 `accuracy_pos`。 -/
theorem accuracy_le_delta_on_block_C11W4
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (j : ℕ) :
    0 < T.accuracy j ∧ ∀ t ∈ Icc (0 : ℝ) (preparedSpatialHorizon (j + 1)),
      T.accuracy j ≤ (T.block (j + 1)).parameters.delta t := by
  refine ⟨(T.extension j).accuracy_pos, fun t ht => ?_⟩
  have hb : 0 ≤ preparedSpatialHorizon (j + 1) := ht.1.trans ht.2
  have hafter := (T.extension j).successor.delta_after (preparedSpatialHorizon (j + 1))
    (preparedSpatialHorizon_lt_succ_C11W4 j)
  rw [← hafter]
  exact (state_delta_lower_bound_C11W4 (T.block (j + 1)) hb).2 t ht

/-- 有限多个正数取有限 min：`J` 之前的所有 `d_j` 有统一正下界。 -/
theorem exists_pos_lower_bound_finite_C11W4 (f : ℕ → ℝ) (hf : ∀ j, 0 < f j) (J : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ j ≤ J, δ₀ ≤ f j := by
  induction J with
  | zero => exact ⟨f 0, hf 0, fun j hj => by rw [Nat.le_zero.mp hj]⟩
  | succ J ih =>
    obtain ⟨δ₀, hδ, hle⟩ := ih
    refine ⟨min δ₀ (f (J + 1)), lt_min hδ (hf _), fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (J + 1) with h | h
    · exact (min_le_left _ _).trans (hle j (Nat.lt_succ_iff.mp h))
    · rw [show j = J + 1 from le_antisymm hj h]
      exact min_le_right _ _

/-- 请求预算在 `[0, T]` 上只涉及有限多个块：前 `J + 1` 个 `d_j` 有统一正下界。 -/
theorem tower_accuracy_lower_bound_finite_C11W4
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (J : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ j ≤ J, δ₀ ≤ T.accuracy j :=
  exists_pos_lower_bound_finite_C11W4 T.accuracy (fun j => (T.extension j).accuracy_pos) J

/-- **对角 schedule 的正下界**：`chainDiagonal_C11A` 的 `delta` 在 `[0, t]` 上 `≥ δ(t) > 0`
（`w1_of_preparedSpatialChain_C11A` 的 `AntitoneOn q.delta (Ici 0)` 与 `q.delta = diagonal.delta`）。 -/
theorem chainDiagonal_delta_lower_bound_C11W4
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) {t : ℝ} (ht : 0 ≤ t) :
    0 < (chainDiagonal_C11A T.toChain).delta t ∧
      ∀ s ∈ Icc (0 : ℝ) t, (chainDiagonal_C11A T.toChain).delta t ≤
        (chainDiagonal_C11A T.toChain).delta s := by
  obtain ⟨F, q, κ, records, ε, C1, C2, hTower, hdiag, -, -, -, hδanti, -⟩ :=
    w1_of_preparedSpatialChain_C11A T.toChain
  refine ⟨(chainDiagonal_C11A T.toChain).delta_pos t ht, fun s hs => ?_⟩
  rw [← hdiag t ht, ← hdiag s hs.1]
  exact (delta_lower_bound_of_antitone_C11W4 q hδanti ht).2 s hs

/-- consumer：`BlockTower` + 逐块 `RequestCofinal` ⇒ 固定请求 `(ε, D, m)` 最终被第 `j` 步 retention
的 fine 参数满足，同时链精度 `d_j ≤ ε`，且前 `J + 1` 步的 `d_j` 有统一正下界。 -/
example (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hcof : ∀ j, RequestCofinal_C11W4 j (T.request j)) (ε D : ℝ) (hε : 0 < ε) (m J : ℕ) :
    (∀ᶠ j : ℕ in atTop, T.accuracy j ≤ ε ∧
      ∀ W : PreparedSpatialStepRetention (T.block j) (T.block (j + 1)) (T.accuracy j)
        (1 / ((j : ℝ) + 2)) (T.request j).epsCut (T.request j).Dcut (T.request j).mcut,
        W.fineParameters.modelAccuracy ≤ ε ∧ D ≤ W.fineParameters.modelRadius ∧
          m ≤ W.fineParameters.modelOrder) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ j ≤ J, δ₀ ≤ T.accuracy j := by
  refine ⟨?_, tower_accuracy_lower_bound_finite_C11W4 T J⟩
  filter_upwards [tower_accuracy_eventually_le_C11W4 T hε,
    tower_fine_request_eventually_C11W4 T hcof hε D m] with j h1 h2
  exact ⟨h1, h2⟩

end GC.LongTime.Ch11
