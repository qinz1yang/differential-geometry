import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# 局域化 ≠ 短窗化：窗口覆盖与 ODE budget（O-CH11-FOOT4 G3，后缀 `_P6F4`；R-C11-17 D-8(iii)）

FOOT3 的 `hderivL / hgradL / hkappaL` 在任意固定 `(T, r)` 上量化，实际调用 `T = 3·B_w`
（`B_w` = P6WB 终端核
`exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB` 的 `∃ Bw`，
经 FOOT3 `terminal_scalar_bound_local_P6F3` 透出）。PBKAPPA / SEEDCL / J10WIRE2 给的是短窗数据
（`β/q`，或 `2·Ctime·Qb·T ≤ 1` 的 ODE ceiling 深度）。
* **κ**（`hkappaL`）：无短窗问题——G2 `hkappaL_of_fresh_P6F4` 走 FRESH 宏观 seed 窗 `[Tn − 1/2, Tn]`，任意 `T`
  的 `[t − T/R_k, t]` eventually 被前缀 `hwin′` 包含。
* **`window_cover_P6F4`**（PROVED，纯区间组合）：深窗 `[t − D, t]` 由 `N` 段长 `β` 的短窗覆盖
  （`D ≤ N·β`，`0 < N`）；每段各用**一次**短窗数据 ⇒ 深窗数据。`window_cover_one_P6F4`：`D ≤ β` 时直接包含。
* **`ode_budget_geometric_P6F4`**（PROVED，算术）：若第 `j` 段的曲率 anchor 只能取上一段 ODE ceiling 的输出
  （ceiling 每段翻倍 ⇒ 第 `j` 段可用深度 `β/2^j`），总深度 `< 2β`——单一 anchor 的分段**不能**越过 `2β`；
  故分段覆盖需要**每段独立的曲率 anchor**（不由上一段 ODE 输出供给）。
* **lead / J10WIRE2 的问题（Bw 能否取成 `6·Ctime·Qb·Bw ≤ 1`）：不能。** `Bw` 是 P6WB 终端核在 history 之前
  取定的 `∃` 常数（依赖 `ε κ C1 C2 Cder Cgrad phi A Cq`），其证明是反证 + blow-up：第 `n` 个反例取
  `Bw n = n + 1 + θ`，需要 `Q_n·(t_n − a_n) ≥ Bw n → ∞`（极限流须 ancient），即 `Bw` 本质上是"足够大"的
  向后抛物深度；核对窗口数据只有向大单调（`Bw` 的数据蕴含更小窗口的数据，反之不然）。没有任何陈述允许把
  `Bw` 压到 `1/(6·Ctime·Qb)`；若要短窗版核，须重证 P6WB 的反证且极限不再 ancient——不可行。
  ⇒ `hstopDeep` / `hdeep` **不能**空真。最小额外前提（BLOCKED repair target）：在格点
  `s_j = t − j·β/R_k`（`β := 1/(2·Ctime·Qb)`，`j < ⌈3·Bw/β⌉`）上的**独立曲率 anchor**——J10WIRE2 端点球控制
  `hball`（`B_{s_j}(trace 点, r/√R_k)` 上 `R ≤ Qb·R_k`）在格点时刻成立（而不只在 `t ↑ σ`）；有了它，每段
  `[s_{j+1}, s_j]` 用一次 `hderivL_short`（`2·Ctime·Qb·β ≤ 1`），`window_cover_P6F4` 拼成 `T = 3·Bw` 的
  `hderivL`。格点 anchor 本身 = U-trace 上向后深度 `3·Bw/R_k` 的有界曲率（BCD 在早先时刻的版本），owner =
  BCD 时间 bootstrap（J10GEN / 后继 FOOT 车道）；不能由导数界 `|∂ₜR| ≤ Ctime·R²` 单独给出（导数界允许 R 在
  整个窗口保持任意大的常数）。
-/

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **窗口覆盖（`_P6F4`，PROVED）**：`[t − D, t]`（`D ≤ N·β`，`0 < β`，`0 < N`）被 `N` 段
`[t − (j+1)β, t − jβ]`（`j < N`）覆盖；每段上成立的谓词在整个深窗上成立。 -/
theorem window_cover_P6F4 {Φ : ℝ → Prop} {t D β : ℝ} (hβ : 0 < β) {N : ℕ} (hN0 : 0 < N)
    (hN : D ≤ N * β)
    (hseg : ∀ j : ℕ, j < N → ∀ v : ℝ, t - (j + 1) * β ≤ v → v ≤ t - j * β → Φ v) :
    ∀ v : ℝ, t - D ≤ v → v ≤ t → Φ v := by
  intro v hv1 hv2
  have hx0 : 0 ≤ (t - v) / β := div_nonneg (by linarith) hβ.le
  have hxN : (t - v) / β ≤ N := by
    rw [div_le_iff₀ hβ]
    linarith
  by_cases hfl : ⌊(t - v) / β⌋₊ < N
  · refine hseg _ hfl v ?_ ?_
    · have h := Nat.lt_floor_add_one ((t - v) / β)
      have h' : t - v < (⌊(t - v) / β⌋₊ + 1) * β := by
        rwa [div_lt_iff₀ hβ] at h
      linarith
    · have h := Nat.floor_le hx0
      have h' : ⌊(t - v) / β⌋₊ * β ≤ t - v := by
        rwa [le_div_iff₀ hβ] at h
      linarith
  · have hge : (N : ℝ) ≤ (t - v) / β := by
      have h := Nat.floor_le hx0
      have h2 : (N : ℝ) ≤ ⌊(t - v) / β⌋₊ := by exact_mod_cast not_lt.mp hfl
      linarith
    have heq : t - v = N * β := by
      have h1 : N * β ≤ t - v := by rwa [le_div_iff₀ hβ] at hge
      have h2 : t - v ≤ N * β := by rwa [div_le_iff₀ hβ] at hxN
      linarith
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    refine hseg M (Nat.lt_succ_self M) v ?_ ?_
    · push_cast at heq ⊢
      linarith
    · push_cast at heq
      have : 0 ≤ β := hβ.le
      nlinarith

/-- **T ≤ β 直接包含（`_P6F4`，PROVED）**：`D ≤ β` 时短窗数据直接覆盖深窗（`window_cover_P6F4`，`N = 1`）。 -/
theorem window_cover_one_P6F4 {Φ : ℝ → Prop} {t D β : ℝ} (hβ : 0 < β) (hD : D ≤ β)
    (hshort : ∀ v : ℝ, t - β ≤ v → v ≤ t → Φ v) :
    ∀ v : ℝ, t - D ≤ v → v ≤ t → Φ v :=
  window_cover_P6F4 hβ Nat.one_pos (by simpa using hD) fun j hj v h1 h2 => by
    obtain rfl : j = 0 := by omega
    exact hshort v (by simpa using h1) (by simpa using h2)

/-- **单一 anchor 的 ODE budget 几何收缩（`_P6F4`，PROVED，算术）**：第 `j` 段可用深度 `β/2^j`
（ceiling 每段翻倍）⇒ 任意有限段总深度 `< 2β`。故深度 `> 2β` 的窗口需要每段独立的曲率 anchor。 -/
theorem ode_budget_geometric_P6F4 {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    ∑ j ∈ Finset.range N, β / 2 ^ j < 2 * β := by
  have h : ∑ j ∈ Finset.range N, β / 2 ^ j = β * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [h]
  have hs : ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j = 2 * (1 - (1 / 2) ^ N) := by
    rw [geom_sum_eq (by norm_num)]
    field_simp
    ring
  have hp : 0 < ((1 : ℝ) / 2) ^ N := pow_pos (by norm_num) N
  rw [hs]
  nlinarith

/-- consumer（G3）：深度 `3·Bw` 的窗口由 `⌈3·Bw/β⌉₊` 段 `β` 短窗覆盖（格点 anchor 给出的每段数据）。 -/
example {Φ : ℝ → Prop} {t Bw β : ℝ} (hβ : 0 < β) (hBw : 0 < Bw)
    (hseg : ∀ j : ℕ, j < ⌈3 * Bw / β⌉₊ → ∀ v : ℝ, t - (j + 1) * β ≤ v → v ≤ t - j * β → Φ v) :
    ∀ v : ℝ, t - 3 * Bw ≤ v → v ≤ t → Φ v := by
  refine window_cover_P6F4 hβ (Nat.ceil_pos.mpr (by positivity)) ?_ hseg
  have h := Nat.le_ceil (3 * Bw / β)
  rwa [div_le_iff₀ hβ] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
