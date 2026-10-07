import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# S-CH11-REPROVE-C (G1)：S9 `recent_cutoff_smallness` 的 3ⁿ 算术

reference：astra `SH/PreparedSpatialRecentCutoff.lean:14–38, 97–101, 118–140`（`activation`、
`nat_le_activation`、`horizon_lt_half_activation`、`cutoff_factor_antitone`、
`exists_activation_band`）与 `SH/PreparedSpatialChain.lean:17–26`（`preparedSpatialHorizon`、
`nat_lt_three_pow`）。这里只剩纯实数算术，不依赖任何 history / chain 结构。

* `fullHorizon_C11RC k`：第 `k` 个 full state 的 horizon（`0, 1, 3, 9, …`）；
* `activation_C11RC k = (5/6)·3ᵏ`：第 `k` 个 successor 的 radius 激活时刻；
* `exists_activation_band_C11RC`：`t ≥ activation (N+1)` 时存在 `k ≥ N` 使
  `activation k < t ≤ activation (k+1)`；
* `fullHorizon_lt_half_activation_C11RC`：`fullHorizon k < activation k / 2`，所以
  `t ∈ (activation k, activation (k+1)]` 且 `s ≥ t/2` 的事件时间 `s` 晚于第 `k` 个 full horizon；
* `cutoffFactor_le_of_ceil_le_C11RC`：`k ≥ ⌈η⁻¹⌉` ⇒ `1/(k+2) ≤ η`。
-/

noncomputable section

namespace GC.LongTime.Ch11

/-- full state `k` 的 horizon：`h 0 = 0`，`h (k+1) = 3ᵏ`（astra `preparedSpatialHorizon`）。 -/
def fullHorizon_C11RC : ℕ → ℝ
  | 0 => 0
  | n + 1 => (3 : ℝ) ^ n

/-- 第 `k` 个 successor 的 radius 激活时刻 `(5/6)·3ᵏ`（astra `activation`）。 -/
def activation_C11RC (n : ℕ) : ℝ := (5 / 6 : ℝ) * 3 ^ n

theorem nat_lt_three_pow_C11RC (n : ℕ) : (n : ℝ) < (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem activation_pos_C11RC (n : ℕ) : 0 < activation_C11RC n :=
  mul_pos (by norm_num) (pow_pos (by norm_num) n)

theorem activation_succ_C11RC (n : ℕ) :
    activation_C11RC (n + 1) = 3 * activation_C11RC n := by
  simp only [activation_C11RC, pow_succ]
  ring

theorem activation_strictMono_C11RC : StrictMono activation_C11RC := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [activation_succ_C11RC]
  linarith [activation_pos_C11RC n]

theorem nat_le_activation_C11RC (n : ℕ) : (n : ℝ) ≤ activation_C11RC n := by
  induction n with
  | zero => norm_num [activation_C11RC]
  | succ n ih =>
    have hsmall : (5 / 6 : ℝ) ≤ activation_C11RC n := by
      have hpow : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      dsimp only [activation_C11RC]
      nlinarith
    rw [activation_succ_C11RC, Nat.cast_add, Nat.cast_one]
    linarith

theorem fullHorizon_lt_half_activation_C11RC (n : ℕ) :
    fullHorizon_C11RC n < activation_C11RC n / 2 := by
  cases n with
  | zero => norm_num [fullHorizon_C11RC, activation_C11RC]
  | succ n =>
    have hp : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
    simp only [fullHorizon_C11RC, activation_C11RC, pow_succ]
    nlinarith

/-- `k ≤ h_k + 1`：前 `k` 个 full state 的 horizon 至少是 `k - 1`（用来从“事件晚于 `h_k`”
推出观察指标 `n ≥ k`）。 -/
theorem nat_le_fullHorizon_add_one_C11RC (k : ℕ) : (k : ℝ) ≤ fullHorizon_C11RC k + 1 := by
  cases k with
  | zero => norm_num [fullHorizon_C11RC]
  | succ n =>
    have h := nat_lt_three_pow_C11RC n
    simp only [fullHorizon_C11RC, Nat.cast_add, Nat.cast_one]
    linarith

theorem fullHorizon_nonneg_C11RC (k : ℕ) : 0 ≤ fullHorizon_C11RC k := by
  cases k with
  | zero => norm_num [fullHorizon_C11RC]
  | succ n => exact (pow_pos (by norm_num) n).le

/-- `t ≥ activation (N+1)` 时，存在 `k ≥ N` 使 `t` 落在第 `k` 个 activation band
`(activation k, activation (k+1)]`。 -/
theorem exists_activation_band_C11RC (N : ℕ) (t : ℝ)
    (ht : activation_C11RC (N + 1) ≤ t) :
    ∃ k : ℕ, N ≤ k ∧ activation_C11RC k < t ∧ t ≤ activation_C11RC (k + 1) := by
  classical
  have hex : ∃ j : ℕ, t ≤ activation_C11RC j :=
    ⟨Nat.ceil t, (Nat.le_ceil t).trans (nat_le_activation_C11RC _)⟩
  cases hfind : Nat.find hex with
  | zero =>
    have hupper : t ≤ activation_C11RC 0 := by simpa only [hfind] using Nat.find_spec hex
    exact False.elim ((not_le_of_gt (activation_strictMono_C11RC (Nat.zero_lt_succ N)))
      (ht.trans hupper))
  | succ k =>
    have hupper : t ≤ activation_C11RC (k + 1) := by
      simpa only [hfind] using Nat.find_spec hex
    refine ⟨k, ?_, ?_, hupper⟩
    · by_contra hNk
      have hlt : activation_C11RC (k + 1) < activation_C11RC (N + 1) :=
        activation_strictMono_C11RC (Nat.succ_lt_succ (lt_of_not_ge hNk))
      exact (not_le_of_gt hlt) (ht.trans hupper)
    · exact lt_of_not_ge (Nat.find_min hex (by rw [hfind]; omega))

theorem cutoffFactor_antitone_C11RC :
    Antitone (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
  intro m n hmn
  have h : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- `k ≥ ⌈η⁻¹⌉` ⇒ `1/(k+2) ≤ η`（`η > 0`）。 -/
theorem cutoffFactor_le_of_ceil_le_C11RC {η : ℝ} (hη : 0 < η) {k : ℕ}
    (hk : Nat.ceil η⁻¹ ≤ k) : 1 / ((k : ℝ) + 2) ≤ η := by
  have hfactor : 1 / (((Nat.ceil η⁻¹ : ℕ) : ℝ) + 2) ≤ η := by
    apply (div_le_iff₀ (by positivity : 0 < ((Nat.ceil η⁻¹ : ℕ) : ℝ) + 2)).mpr
    have hm := mul_le_mul_of_nonneg_left (Nat.le_ceil η⁻¹) hη.le
    rw [mul_inv_cancel₀ (ne_of_gt hη)] at hm
    nlinarith
  exact (cutoffFactor_antitone_C11RC hk).trans hfactor

end GC.LongTime.Ch11
