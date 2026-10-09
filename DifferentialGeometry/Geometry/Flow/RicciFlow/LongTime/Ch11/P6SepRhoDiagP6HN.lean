import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscaleKSepRhoP6HN

/-!
# (W) 的对角抽取 ⇒ 窗口形 `T₀` 满足 kernel `hT₀`（O-CH11-HNOT-LOCALDT G4，后缀 `_P6HN`）

G3 `hscaleK_of_sepRhoPlus_P6HN` 的过去窗前提 `hpast` 是 (SEP-ρ⁺) 左支 (W)（`∀ B ∀ᶠ n`）
在单个 `n`、窗口 `B_n` 上的形。本文件给出两件标准事实：
* `exists_tendsto_eventually_P6HN`：`∀ k, ∀ᶠ n, P k n` ⇒ `∃ B → ∞, ∀ᶠ n, P (B n) n`
  （`Nat.findGreatest` 对角抽取；`P` 不需单调）。
* `hT₀_of_tendsto_P6HN`：`B_n → ∞`、`R n > 0` ⇒ `T₀ n := σ n − B_n/R n` 满足 kernel 的
  `hT₀ : ∀ B, ∀ᶠ n, T₀ n ≤ σ n − B/R n`（`NotKKernelNoJ10_P6JB`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **对角抽取（`_P6HN`，PROVED）**：`∀ k, ∀ᶠ n, P k n` ⇒ 存在 `B : ℕ → ℕ`，`B → ∞` 且 `∀ᶠ n, P (B n) n`。 -/
theorem exists_tendsto_eventually_P6HN {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ B : ℕ → ℕ, Tendsto B atTop atTop ∧ ∀ᶠ n in atTop, P (B n) n := by
  classical
  choose N hN using fun k => eventually_atTop.mp (h k)
  set M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N with hMdef
  have hNM : ∀ k, N k ≤ M k := fun k =>
    Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hMmono : Monotone M := fun a b hab =>
    Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hab))
  refine ⟨fun n => Nat.findGreatest (fun k => M k ≤ n) n, ?_, ?_⟩
  · refine tendsto_atTop_atTop.mpr fun K => ⟨max K (M K), fun n hn => ?_⟩
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  · refine eventually_atTop.mpr ⟨M 0, fun n hn => ?_⟩
    have hspec : M (Nat.findGreatest (fun k => M k ≤ n) n) ≤ n :=
      Nat.findGreatest_spec (P := fun k => M k ≤ n) (Nat.zero_le n) hn
    exact hN _ n ((hNM _).trans hspec)

/-- **窗口形 `T₀` 满足 kernel `hT₀`（`_P6HN`，PROVED）**。 -/
theorem hT₀_of_tendsto_P6HN {σ R : ℕ → ℝ} (hR : ∀ n, 0 < R n) {B : ℕ → ℕ}
    (hB : Tendsto B atTop atTop) :
    ∀ b : ℝ, ∀ᶠ n in atTop, σ n - (B n : ℝ) / R n ≤ σ n - b / R n := by
  intro b
  filter_upwards [hB.eventually_ge_atTop ⌈b⌉₊] with n hn
  have hb : b ≤ (B n : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hn)
  have := div_le_div_of_nonneg_right hb (hR n).le
  linarith

/-- **`exists_diag_window_P6HN`（PROVED，供 KSLABK / DEPTH）**：(W) 的 `∀ k ∀ᶠ n` ⇒ 对角窗口 `B_n → ∞`，
`T₀ n := σ n − B_n/R n` 满足 kernel `hT₀`，且 eventually (W_{B_n})。 -/
theorem exists_diag_window_P6HN {σ R : ℕ → ℝ} (hR : ∀ n, 0 < R n) {W : ℕ → ℕ → Prop}
    (hW : ∀ k, ∀ᶠ n in atTop, W k n) :
    ∃ B : ℕ → ℕ, Tendsto B atTop atTop ∧
      (∀ b : ℝ, ∀ᶠ n in atTop, σ n - (B n : ℝ) / R n ≤ σ n - b / R n) ∧
      ∀ᶠ n in atTop, W (B n) n := by
  obtain ⟨B, hB, hev⟩ := exists_tendsto_eventually_P6HN hW
  exact ⟨B, hB, hT₀_of_tendsto_P6HN hR hB, hev⟩

/-- consumer（`_P6HN`）：窗口形 `T₀` 逐字是 kernel `hT₀` 槽（`∀ B : ℝ, ∀ᶠ n, T₀ n ≤ σ n − B / R n`）。 -/
example {σ R : ℕ → ℝ} (hR : ∀ n, 0 < R n) {W : ℕ → ℕ → Prop} (hW : ∀ k, ∀ᶠ n in atTop, W k n) :
    ∃ T₀ : ℕ → ℝ, (∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ σ n - B / R n) := by
  obtain ⟨B, -, hT, -⟩ := exists_diag_window_P6HN (σ := σ) hR hW
  exact ⟨fun n => σ n - (B n : ℝ) / R n, hT⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
