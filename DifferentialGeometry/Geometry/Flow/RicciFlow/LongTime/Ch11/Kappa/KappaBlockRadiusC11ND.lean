import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W

/-!
# astra 链：`nr(3^k) = 块半径`，块比 ⇔ lookahead 下界（S-CH11-DOUBLE G1，后缀 `_C11ND`）

**桥（无条件定理）**：对 astra `PreparedSpatialChain S` 及其极限参数 `q`（`hobs` =
`exists_surgery_with_retained_raw_caps`
的 `q.neckRadius t = (S.observation n).parameters.neckRadius t`，`t ∈ [0, n]`，逐字），

  `q.neckRadius (3^k) = (S.state (k+1)).radius`。

证明：`radius_after`（state `k+1` 的 `E = 3^k`）+ `radius_before_activation`（`3^k ≤ (5/6)·3^j`，`j ≥ k+1`）
把 state `m+1`（`m = 3^k`，观察 horizon）逐级拉回 state `k+1`。所以 `nr` 在块边界 `3^k` 上的值就是块半径
`rad(k+1) = (T.block (k+1)).radius`，而 `rad(k+2) = ℓ_{k+1}.rNext`（`PhysicalExtension.radius_eq`）。

**G1 发现（精确缺口）**：C11W 的 `BlockStep_C11W` / astra Step
（`exists_prepared_spatial_step_…_with_reserve_quality`）对 `rNext` 只给
`0 < rNext ≤ X.radius`、`Qall ≤ rNext⁻²`、`rNext·√Qall ≤ 100·cMax`；证明里
`rNext := min rSupply (100·cMax/√QallNew)`，`(rSupply, QallNew)` 来自
`exists_prepared_two_overlap_extension_with_closed_seam_…` 的存在量词（只有 `rSupply ≤ L.radius`，无下界）。
所以 **相邻块半径比有界不能从 BlockStep 推出**；它是 BlockStep 之外的新输入，精确形（tower 版）是

  `hlook : ∃ C k₀, ∀ j ≥ k₀, (T.block j).radius ≤ C * (T.lookahead j).rNext`
  （即 `ℓ_j.rNext ≥ X_j.radius / C`，"rNext 不低于上一块半径的固定比例"）。

本文件把它接到 nr 的块比：`nrBlockRatio_of_lookahead_C11ND`（⇒ `nr(3^k) ≤ C·nr(3^(k+1))`）；
块比 ⇒ 逐字 `hnrDoubling` 在 G2（`KappaNrDoublingC11ND`、`KappaDoublingEndToEndC11ND`）。
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

/-- **桥**：`q.neckRadius (3^k) = (S.state (k+1)).radius`。 -/
theorem neckRadius_pow_eq_stateRadius_C11ND {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t) (k : ℕ) :
    q.neckRadius ((3 : ℝ) ^ k) = (S.state (k + 1)).radius := by
  have hstate : ∀ j : ℕ, k + 1 ≤ j →
      (S.state j).parameters.neckRadius ((3 : ℝ) ^ k) = (S.state (k + 1)).radius := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact (S.state (k + 1)).radius_after _ le_rfl
    | succ j hj ih =>
      have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) hj
      have hp : (0 : ℝ) < 3 ^ k := pow_pos (by norm_num) k
      have h4 : (3 : ℝ) ^ k ≤ 5 / 6 * 3 ^ j := by
        rw [pow_succ] at h3
        nlinarith
      rw [(S.successor j).radius_before_activation _ h4]
      exact ih
  have hk : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  have hm : ((3 ^ k : ℕ) : ℝ) = (3 : ℝ) ^ k := by push_cast; ring
  have h1 := hobs (3 ^ k) ((3 : ℝ) ^ k) ⟨by positivity, hm.ge⟩
  rw [h1]
  exact hstate (3 ^ k + 1) (by omega)

/-- 链上块半径比有界 ⇒ `nr` 的块比有界（`nr (3^k) ≤ C · nr (3^(k+1))`）。 -/
theorem nrBlockRatio_of_stateRadii_C11ND {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t)
    (hrad : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (S.state (k + 1)).radius ≤ C' * (S.state (k + 1 + 1)).radius) :
    ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      q.neckRadius ((3 : ℝ) ^ k) ≤ C' * q.neckRadius ((3 : ℝ) ^ (k + 1)) := by
  obtain ⟨C', k₀, h⟩ := hrad
  refine ⟨C', k₀, fun k hk => ?_⟩
  rw [neckRadius_pow_eq_stateRadius_C11ND S q hobs k,
    neckRadius_pow_eq_stateRadius_C11ND S q hobs (k + 1)]
  exact h k hk

/-- **tower 版（G1 的精确缺口形）**：lookahead 下界 `rNext ≥ X.radius / C`（`j ≥ k₀`）⇒ `nr` 的块比有界。
`hlook` 不是 `BlockStep_C11W` 的推论（见文件头）。 -/
theorem nrBlockRatio_of_lookahead_C11ND {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : NNReal} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) (q : CutoffParameters)
    (hobs : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (T.toChain.observation n).parameters.neckRadius t)
    (hlook : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) :
    ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      q.neckRadius ((3 : ℝ) ^ k) ≤ C' * q.neckRadius ((3 : ℝ) ^ (k + 1)) := by
  obtain ⟨C', k₀, h⟩ := hlook
  refine nrBlockRatio_of_stateRadii_C11ND T.toChain q hobs ⟨C', k₀ + 1, fun k hk => ?_⟩
  have h1 := h (k + 1) (by omega)
  rw [← (T.extension (k + 1)).radius_eq] at h1
  exact h1

end GC.LongTime.Ch11
