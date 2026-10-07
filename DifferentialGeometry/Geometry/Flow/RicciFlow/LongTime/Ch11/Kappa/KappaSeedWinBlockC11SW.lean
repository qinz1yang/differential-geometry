import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain

/-!
# seed-window 的块算术（O-CH11-SEEDWIN-P G1，后缀 `_C11SW`）

activation `a_k := (5/6)·3^k` 是 `PreparedSpatialChain.successor k` 的结构参数；极限参数 `q` 的
`neckRadius` 在 band `B_k := (a_k, a_{k+1}]` 上常值 `= (S.state (k+1)).radius`
（`neckRadius_eq_on_band_C11SW`，经 `hobs`，同 C11ND 的证明形）。

* `seedWin_of_sameBlock_C11SW`：`t − r²/2` 与 `t` 同块 + `nr t ≤ r` ⇒ `nr (t − r²/2) ≤ r`（单项）；
  `eventually_seedWin_of_eventually_sameBlock_C11SW`（序列版）。
* `window_band_C11SW`：`2r² < t` ⇒ 窗口 `[t − r²/2, t]` 至多跨一个 activation（块长 `2a_k > r²/2`，
  块长下界来自结构字段，不需显式前提）。
* `window_value_C11SW` / `seedWin_or_fresh_C11SW`：单点二分——同块（`nr` 两端相等）或 crossing
  `t − r²/2 ≤ a_k < t`（`nr (t − r²/2) = nr a_k`，旧块半径）；后者且 `r < nr a_k` 即 fresh-activation 支。
这里不声称 selection 能避开 crossing（见 design-C11-seedwin-producer §1）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

/-- **同块单项**：`nr` 在块 `(b k, b (k+1)]` 上常值；`t − r²/2` 与 `t` 同块且 `nr t ≤ r` ⇒
`nr (t − r²/2) ≤ r`。 -/
theorem seedWin_of_sameBlock_C11SW {nr : ℝ → ℝ} {b c : ℕ → ℝ}
    (hconst : ∀ k w, b k < w → w ≤ b (k + 1) → nr w = c k) {t r : ℝ} {k : ℕ}
    (hleft : b k < t - r ^ 2 / 2) (hright : t ≤ b (k + 1)) (hle : nr t ≤ r) :
    nr (t - r ^ 2 / 2) ≤ r := by
  have hsub : t - r ^ 2 / 2 ≤ t := by nlinarith [sq_nonneg r]
  rw [hconst k _ hleft (hsub.trans hright), ← hconst k t (hleft.trans_le hsub) hright]
  exact hle

/-- **同块序列版**：最终同块 + 最终 `nr t ≤ r` ⇒ `hseedWin`。 -/
theorem eventually_seedWin_of_eventually_sameBlock_C11SW {nr : ℝ → ℝ} {b c : ℕ → ℝ}
    (hconst : ∀ k w, b k < w → w ≤ b (k + 1) → nr w = c k) {t r : ℕ → ℝ}
    (hsame : ∀ᶠ n in atTop, ∃ k, b k < t n - r n ^ 2 / 2 ∧ t n ≤ b (k + 1))
    (hle : ∀ᶠ n in atTop, nr (t n) ≤ r n) :
    ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n := by
  filter_upwards [hsame, hle] with n hn hl
  obtain ⟨k, h1, h2⟩ := hn
  exact seedWin_of_sameBlock_C11SW hconst h1 h2 hl

/-- 每个 `t > 5/6` 落在某个 band `(a_k, a_{k+1}]`。 -/
theorem exists_band_C11SW {t : ℝ} (ht : (5 / 6 : ℝ) < t) :
    ∃ k : ℕ, (5 / 6 : ℝ) * 3 ^ k < t ∧ t ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) := by
  classical
  have hex : ∃ j : ℕ, t ≤ (5 / 6 : ℝ) * 3 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (6 / 5 * t) (by norm_num : (1 : ℝ) < 3)
    exact ⟨j, by linarith⟩
  have hfind := Nat.find_spec hex
  cases hj : Nat.find hex with
  | zero =>
    rw [hj, pow_zero, mul_one] at hfind
    linarith
  | succ k =>
    refine ⟨k, ?_, ?_⟩
    · exact lt_of_not_ge (Nat.find_min hex (show k < Nat.find hex by omega))
    · rw [hj] at hfind
      exact hfind

/-- **窗口至多跨一个 activation**：`2r² < t ∈ B_{k+1}` ⇒ 同块（`a_{k+1} < t − r²/2`）或
`t − r²/2 ∈ B_k`（只跨 `a_{k+1}`）。 -/
theorem window_band_C11SW {t r : ℝ} {k : ℕ} (htime : 2 * r ^ 2 < t)
    (ht : (5 / 6 : ℝ) * 3 ^ (k + 1) < t) :
    (5 / 6 : ℝ) * 3 ^ (k + 1) < t - r ^ 2 / 2 ∨
      ((5 / 6 : ℝ) * 3 ^ k < t - r ^ 2 / 2 ∧ t - r ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) := by
  by_cases h : (5 / 6 : ℝ) * 3 ^ (k + 1) < t - r ^ 2 / 2
  · exact Or.inl h
  · refine Or.inr ⟨?_, le_of_not_gt h⟩
    have hp : (0 : ℝ) < 3 ^ k := pow_pos (by norm_num) k
    rw [pow_succ] at ht
    nlinarith

/-- **两端取值二分**（band 常值的 `nr`，`t > 5/2`）：`nr (t − r²/2) = nr t`，或窗口跨 `a_k`
（`t − r²/2 ≤ a_k < t`）且 `nr (t − r²/2) = nr a_k`（旧块值）。 -/
theorem window_value_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℝ} (htime : 2 * r ^ 2 < t) (hlate : (5 / 2 : ℝ) < t) :
    nr (t - r ^ 2 / 2) = nr t ∨
      ∃ k : ℕ, t - r ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k ∧ (5 / 6 : ℝ) * 3 ^ k < t ∧
        nr (t - r ^ 2 / 2) = nr ((5 / 6 : ℝ) * 3 ^ k) := by
  obtain ⟨j, hj1, hj2⟩ := exists_band_C11SW (by linarith : (5 / 6 : ℝ) < t)
  cases j with
  | zero => norm_num at hj2; linarith
  | succ k =>
    have hsub : t - r ^ 2 / 2 ≤ t := by nlinarith [sq_nonneg r]
    rcases window_band_C11SW htime hj1 with hsame | ⟨hc1, hc2⟩
    · left
      rw [hconst (k + 1) _ hsame (hsub.trans hj2), hconst (k + 1) t hj1 hj2]
    · right
      have hp : (0 : ℝ) < 3 ^ k := pow_pos (by norm_num) k
      have hak : (5 / 6 : ℝ) * 3 ^ k < (5 / 6 : ℝ) * 3 ^ (k + 1) := by
        rw [pow_succ]
        nlinarith
      refine ⟨k + 1, hc2, hj1, ?_⟩
      rw [hconst k _ hc1 hc2, hconst k _ hak le_rfl]

/-- **单点 seed-window 二分**：`nr t ≤ r` 时，`nr (t − r²/2) ≤ r`，或 fresh-activation：
窗口跨 `a_k` 且 `r < nr a_k`（旧块半径大于种子尺度）。 -/
theorem seedWin_or_fresh_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℝ} (htime : 2 * r ^ 2 < t) (hlate : (5 / 2 : ℝ) < t) (hle : nr t ≤ r) :
    nr (t - r ^ 2 / 2) ≤ r ∨
      ∃ k : ℕ, t - r ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k ∧ (5 / 6 : ℝ) * 3 ^ k < t ∧
        r < nr ((5 / 6 : ℝ) * 3 ^ k) := by
  rcases window_value_C11SW hconst htime hlate with heq | ⟨k, hk1, hk2, hk3⟩
  · exact Or.inl (heq ▸ hle)
  · by_cases hr : nr ((5 / 6 : ℝ) * 3 ^ k) ≤ r
    · exact Or.inl (hk3 ▸ hr)
    · exact Or.inr ⟨k, hk1, hk2, lt_of_not_ge hr⟩

/-- **band 常值（chain 级）**：astra 链的极限参数 `q`（`hobs` 同 C11ND）在 `(a_k, a_{k+1}]` 上
`q.neckRadius w = (S.state (k+1)).radius`。 -/
theorem neckRadius_eq_on_band_C11SW {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t) (k : ℕ) (w : ℝ)
    (hleft : (5 / 6 : ℝ) * 3 ^ k < w) (hright : w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1)) :
    q.neckRadius w = (S.state (k + 1)).radius := by
  have hstate : ∀ j : ℕ, k + 1 ≤ j →
      (S.state j).parameters.neckRadius w = (S.state (k + 1)).radius := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact (S.successor k).radius_after_activation w hleft
    | succ j hj ih =>
      have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) hj
      rw [(S.successor j).radius_before_activation w (hright.trans (by linarith))]
      exact ih
  have hw0 : 0 ≤ w := le_trans (by positivity) hleft.le
  have hwn : w ≤ ((max k (Nat.ceil w) : ℕ) : ℝ) :=
    (Nat.le_ceil w).trans (by exact_mod_cast le_max_right _ _)
  rw [hobs (max k (Nat.ceil w)) w ⟨hw0, hwn⟩]
  exact hstate (max k (Nat.ceil w) + 1) (Nat.succ_le_succ (le_max_left _ _))

/-- **chain 级 consumer**：astra 极限参数上，`2r² < t`、`t > 5/2`、`nr t ≤ r` ⇒ seed-window 单项
或 fresh-activation（旧块半径 `(S.state k).radius > r`，以 `q.neckRadius a_k` 表出）。 -/
theorem seedWin_or_fresh_chain_C11SW {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t)
    {t r : ℝ} (htime : 2 * r ^ 2 < t) (hlate : (5 / 2 : ℝ) < t) (hle : q.neckRadius t ≤ r) :
    q.neckRadius (t - r ^ 2 / 2) ≤ r ∨
      ∃ k : ℕ, t - r ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k ∧ (5 / 6 : ℝ) * 3 ^ k < t ∧
        r < q.neckRadius ((5 / 6 : ℝ) * 3 ^ k) :=
  seedWin_or_fresh_C11SW (c := fun k => (S.state (k + 1)).radius)
    (neckRadius_eq_on_band_C11SW S q hobs) htime hlate hle

end GC.LongTime.Ch11
