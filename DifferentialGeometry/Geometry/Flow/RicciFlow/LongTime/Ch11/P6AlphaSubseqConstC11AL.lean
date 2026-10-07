import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# (α) 路线 G4：子列紧性 ⇒ 统一常数 + `∀ᶠ n`（O-CH11-ALPHA G4，后缀 `_C11AL`）

addendum `design-C11-alpha-20261007-addendum_C11AL.md` A5 的"子列论证"：树内 driver
（`exists_subseq_forall_depthExtendable_bcadC_P6L2` / window anchor）只给**子列**上的常数；hscalW / hscalU 的
合同形是 `∃ C, ∀ᶠ n`（`C` 在 `n` 前）。本文件给出通用转换（逻辑骨架 = "一次 compactness 给统一常数"）：

* `exists_const_eventually_of_subseq_C11AL`：`P C n` 关于 `C` 单调；若**每个**子列 `φ` 都有子子列 `ψ` 与常数 `C`
  使 `∀ᶠ k, P C (φ (ψ k))`，则 `∃ C, ∀ᶠ n, P C n`。证明：反设 `∀ C, ∃ᶠ n, ¬ P C n`，对 `C = k` 抽子列
  （`Filter.extraction_forall_of_frequently`），子子列上 `ψ k ≥ C` 后单调性矛盾。
* `exists_const_ge_one_eventually_of_subseq_C11AL`：同上，并取 `1 ≤ C`（hscalW / HU 的 `1 ≤ C` 字段）。
-/

set_option autoImplicit false

open Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **子列紧性 ⇒ 统一常数（`_C11AL`）**：`P C n` 关于 `C` 单调递增；每个子列都有子子列与常数使 `P` 最终成立
⇒ 存在单个常数 `C` 使 `P C n` 对原序列最终成立。 -/
theorem exists_const_eventually_of_subseq_C11AL (P : ℝ → ℕ → Prop)
    (hmono : ∀ (C C' : ℝ) (n : ℕ), C ≤ C' → P C n → P C' n)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C : ℝ, ∀ᶠ k in atTop, P C (φ (ψ k))) :
    ∃ C : ℝ, ∀ᶠ n in atTop, P C n := by
  by_contra hcon
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, ¬ P (k : ℝ) n := by
    intro k
    by_contra hk
    exact hcon ⟨(k : ℝ), not_frequently.mp hk |>.mono fun _ h => not_not.mp h⟩
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_frequently hfreq
  obtain ⟨ψ, hψ, C, hC⟩ := hsub φ hφ
  have hψC : ∀ᶠ k in atTop, C ≤ ((ψ k : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop).eventually_ge_atTop C
  obtain ⟨k, hk1, hk2⟩ := (hC.and hψC).exists
  exact hφP (ψ k) (hmono C _ _ hk2 hk1)

/-- **同上，取 `1 ≤ C`（`_C11AL`）**：hscalW / `HU_P6M5` 的常数字段形 `∃ C, 1 ≤ C ∧ ∀ᶠ n, …`。 -/
theorem exists_const_ge_one_eventually_of_subseq_C11AL (P : ℝ → ℕ → Prop)
    (hmono : ∀ (C C' : ℝ) (n : ℕ), C ≤ C' → P C n → P C' n)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C : ℝ, ∀ᶠ k in atTop, P C (φ (ψ k))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop, P C n := by
  obtain ⟨C, hC⟩ := exists_const_eventually_of_subseq_C11AL P hmono hsub
  exact ⟨max C 1, le_max_right _ _, hC.mono fun n h => hmono C _ n (le_max_left _ _) h⟩

/-- consumer：`P C n := a n ≤ C`（`a` 有界于每个子列的子子列）⇒ `a` 最终有统一上界 `C ≥ 1`。 -/
example (a : ℕ → ℝ)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C : ℝ, ∀ᶠ k in atTop, a (φ (ψ k)) ≤ C) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop, a n ≤ C :=
  exists_const_ge_one_eventually_of_subseq_C11AL (fun C n => a n ≤ C)
    (fun _ _ _ hCC' h => h.trans hCC') hsub

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
