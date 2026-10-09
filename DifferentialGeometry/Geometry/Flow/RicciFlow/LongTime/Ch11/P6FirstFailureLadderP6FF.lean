import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# FIRSTFAIL G3 见证：A-ladder 的鸽笼稳定层（`_P6FF`，PROVED，只 import Mathlib）

Core（`CanonicalLateTimeCore_P6X`）时间归纳的 A-regress：earlier seed
（`hasSmallParabolicCurvature.earlier_seed_on_half_depth`，尺度 `r/100`、体积常数 `512·e⁵⁷·A`）
只对 `Core(λ·A)`（`λ = 512·e⁵⁷`）合格，而 slab-first 对固定 `A` 只给更早 slab 上的 `Core(A)`；
`Core(A)` 对 `A` 反单调（球更大、体积门槛更低 ⇒ 更强 ⇒ 更早失败）。

鸽笼：令 `k m` = `Core(λ^m·A₀)` 的首个失败 slab（对 `m` 反单调），则存在 `m ≤ k 0` 使
`k (m+1) = k m`，即第 `m` 层失败点之前的前缀在第 `m+1` 层干净（`exists_stable_level_P6FF`）。
代价：`m` 只被 `k 0`（≤ eventCount）控制，层 `λ^m·A₀` 随 `n` 无界 ⇒ kernel 的 κ（体积 `A⁻¹r³`）退化。
故 Core 时间归纳要闭合还缺"窗口内 slab 数一致有界"——见 state-O-CH11-FIRSTFAIL G3。
-/

set_option autoImplicit false

namespace GC.LongTime.Ch11

/-- **鸽笼稳定层（PROVED）**：反单调 `k : ℕ → ℕ` 在 `m ≤ k 0` 处有 `k (m + 1) = k m`。 -/
theorem exists_stable_level_P6FF (k : ℕ → ℕ) (hk : Antitone k) :
    ∃ m ≤ k 0, k (m + 1) = k m := by
  by_contra h
  push Not at h
  have hstep : ∀ m ≤ k 0, k (m + 1) < k m := fun m hm =>
    lt_of_le_of_ne (hk (Nat.le_succ m)) (h m hm)
  have hdec : ∀ m ≤ k 0 + 1, k m + m ≤ k 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hstep m (by omega)
      omega
  have := hdec (k 0 + 1) le_rfl
  omega

/-- **层数上界（PROVED）**：稳定层 `m` 满足 `λ^m ≤ λ^(k 0)`（`1 ≤ λ`）——A-ladder 的层只被首个失败 slab
指标控制（随 eventCount 无界）。 -/
theorem stable_level_pow_le_P6FF (k : ℕ → ℕ) (hk : Antitone k) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∃ m, k (m + 1) = k m ∧ lam ^ m ≤ lam ^ k 0 := by
  obtain ⟨m, hm, hkm⟩ := exists_stable_level_P6FF k hk
  exact ⟨m, hkm, pow_le_pow_right₀ hlam hm⟩

end GC.LongTime.Ch11
