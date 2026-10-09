import Mathlib.Analysis.SpecificLimits.Basic

/-!
# 深度归纳期 4 / R4 E2a（后缀 `_P6DP4E2`）：跨族对角化的通用件

BCDBOOT hTR 合同按「∀ T r, ∃ K, body(T, r, K)」的量词序反证：(T, r) 固定，对每个 `m`（K = m）有一族数据，
其坏性是 `∃ᶠ k`，各个 eventual 条件是 `∀ T > 0, ∀ᶠ k`。本文件给出与数据形状无关的对角化：
* `exists_diag_pick_P6DP4E2`：逐 `m` 选 `κ m`，使其同时满足坏、`E m (m+1)`（eventual 条件在阈值 `m+1` 处）、
  `F m (m+1)`（发散量 `≥ m+1`）以及 `m ≤ κ m`；
* `eventually_of_diag_P6DP4E2`：若 `E m` 对阈值单调，则对角族上 `∀ T > 0, ∀ᶠ m, E m T (κ m)`（hwin、半深度、hT₀ 型）；
* `tendsto_of_diag_P6DP4E2`：对角族上 `L_m (κ m) ≥ m+1`，因而 `→ ∞`（L、`R·(σ − …)`、`√R/200` 型）。
只 import Mathlib；不涉及任何几何前提。具体实例化（内联 body 的否定 → choose → 对角 → 调 E1）见 state。
-/

set_option autoImplicit false

open Filter

namespace GC.LongTime.Ch11

/-- **对角取点（`_P6DP4E2`）**：逐 `m`：坏 `∃ᶠ k`，eventual 族 `∀ T > 0, ∀ᶠ k, E m T k`，发散量 `∀ᶠ k, F m T k`
（对每个阈值 T）⇒ `κ m` 满足坏、`E m (m+1)`、`F m (m+1)`，且 `m ≤ κ m`。 -/
theorem exists_diag_pick_P6DP4E2 {Bad : ℕ → ℕ → Prop} {E Fd : ℕ → ℝ → ℕ → Prop}
    (hB : ∀ m, ∃ᶠ k in atTop, Bad m k) (hE : ∀ m (T : ℝ), 0 < T → ∀ᶠ k in atTop, E m T k)
    (hF : ∀ m (T : ℝ), ∀ᶠ k in atTop, Fd m T k) :
    ∃ κ : ℕ → ℕ, ∀ m, Bad m (κ m) ∧ E m ((m : ℝ) + 1) (κ m) ∧ Fd m ((m : ℝ) + 1) (κ m) ∧
      m ≤ κ m := by
  have h : ∀ m, ∃ k, Bad m k ∧ E m ((m : ℝ) + 1) k ∧ Fd m ((m : ℝ) + 1) k ∧ m ≤ k := fun m =>
    ((hB m).and_eventually ((hE m ((m : ℝ) + 1) (by positivity)).and
      ((hF m ((m : ℝ) + 1)).and (eventually_ge_atTop m)))).exists
  choose κ hκ using h
  exact ⟨κ, hκ⟩

/-- **对角族上的 eventual 条件（`_P6DP4E2`）**：`E m T` 对阈值反单调（`T ≤ T′`、`E m T′ ⇒ E m T`），
`E m (m+1) (κ m)` 逐 `m` 成立 ⇒ `∀ T > 0, ∀ᶠ m, E m T (κ m)`。 -/
theorem eventually_of_diag_P6DP4E2 {E : ℕ → ℝ → ℕ → Prop} {κ : ℕ → ℕ}
    (hmono : ∀ m (T T' : ℝ) k, T ≤ T' → E m T' k → E m T k)
    (hdiag : ∀ m, E m ((m : ℝ) + 1) (κ m)) :
    ∀ T : ℝ, 0 < T → ∀ᶠ m in atTop, E m T (κ m) := by
  intro T _
  obtain ⟨N, hN⟩ := exists_nat_ge T
  filter_upwards [eventually_ge_atTop N] with m hm
  refine hmono m T _ (κ m) ?_ (hdiag m)
  have : (N : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- **对角族上的发散（`_P6DP4E2`）**：`(m : ℝ) + 1 ≤ L m (κ m)` 逐 `m` ⇒ `m ↦ L m (κ m)` 趋于 `∞`。 -/
theorem tendsto_of_diag_P6DP4E2 {L : ℕ → ℕ → ℝ} {κ : ℕ → ℕ}
    (hdiag : ∀ m : ℕ, (m : ℝ) + 1 ≤ L m (κ m)) :
    Tendsto (fun m : ℕ => L m (κ m)) atTop atTop := by
  refine tendsto_atTop_mono hdiag ?_
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- **consumer（`_P6DP4E2`）**：典型实例——坏 `∃ᶠ`、hwin 型 eventual 条件 `a m k ≤ s m k − T / R m k`
（对 T 反单调，需 `0 < R`）、发散量 `L m k → ∞` 逐 `m` ⇒ 对角族同时坏、`∀ T > 0, ∀ᶠ m` hwin、`L → ∞`。 -/
example {Bad : ℕ → ℕ → Prop} {a s R L : ℕ → ℕ → ℝ} (hR : ∀ m k, 0 < R m k)
    (hB : ∀ m, ∃ᶠ k in atTop, Bad m k)
    (hwin : ∀ m (T : ℝ), 0 < T → ∀ᶠ k in atTop, a m k ≤ s m k - T / R m k)
    (hL : ∀ m, Tendsto (L m) atTop atTop) :
    ∃ κ : ℕ → ℕ, (∀ m, Bad m (κ m)) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ m in atTop, a m (κ m) ≤ s m (κ m) - T / R m (κ m)) ∧
      Tendsto (fun m => L m (κ m)) atTop atTop := by
  obtain ⟨κ, hκ⟩ := exists_diag_pick_P6DP4E2 (Bad := Bad)
    (E := fun m T k => a m k ≤ s m k - T / R m k) (Fd := fun m T k => T ≤ L m k) hB hwin
    (fun m T => (hL m).eventually_ge_atTop T)
  refine ⟨κ, fun m => (hκ m).1, ?_, tendsto_of_diag_P6DP4E2 fun m => (hκ m).2.2.1⟩
  refine eventually_of_diag_P6DP4E2 (E := fun m T k => a m k ≤ s m k - T / R m k) ?_
    fun m => (hκ m).2.1
  intro m T T' k hTT' h
  have : T / R m k ≤ T' / R m k := div_le_div_of_nonneg_right hTT' (hR m k).le
  linarith

end GC.LongTime.Ch11
