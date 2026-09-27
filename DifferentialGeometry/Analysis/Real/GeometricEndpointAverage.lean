import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace DifferentialGeometry.Analysis

private theorem sum_sq_add_last_le_four_mul_sum
    (u e : ℕ → ℝ) (n : ℕ) (hinit : u 0 ^ 2 ≤ e 0)
    (hrec : ∀ j < n, u (j + 1) ^ 2 ≤ u j ^ 2 / 2 + 2 * e (j + 1)) :
    (∑ j ∈ Finset.range (n + 1), u j ^ 2) + u n ^ 2 ≤
      4 * ∑ j ∈ Finset.range (n + 1), e j := by
  revert hrec
  induction n with
  | zero =>
    intro _
    simp only [zero_add, Finset.sum_range_one]
    nlinarith [sq_nonneg (u 0)]
  | succ n ih =>
    intro hrec
    have hprev := ih (fun j hj => hrec j (Nat.lt_succ_of_lt hj))
    have hnext := hrec n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ (fun j => u j ^ 2) (n + 1),
      Finset.sum_range_succ e (n + 1)]
    nlinarith only [hprev, hnext]

theorem sum_sq_le_four_mul_sum_of_sq_le_half_add
    (u e : ℕ → ℝ) (n : ℕ) (hinit : u 0 ^ 2 ≤ e 0)
    (hrec : ∀ j < n, u (j + 1) ^ 2 ≤ u j ^ 2 / 2 + 2 * e (j + 1)) :
    (∑ j ∈ Finset.range (n + 1), u j ^ 2) ≤
      4 * ∑ j ∈ Finset.range (n + 1), e j := by
  have h := sum_sq_add_last_le_four_mul_sum u e n hinit hrec
  linarith [sq_nonneg (u n)]

theorem exists_sq_le_four_mul_sum_div_of_sq_le_half_add
    (u e : ℕ → ℝ) (n : ℕ) (hinit : u 0 ^ 2 ≤ e 0)
    (hrec : ∀ j < n, u (j + 1) ^ 2 ≤ u j ^ 2 / 2 + 2 * e (j + 1)) :
    ∃ j ≤ n, u j ^ 2 ≤
      (4 * ∑ i ∈ Finset.range (n + 1), e i) / (n + 1 : ℝ) := by
  have hsum := sum_sq_le_four_mul_sum_of_sq_le_half_add u e n hinit hrec
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hconstant :
      (∑ _j ∈ Finset.range (n + 1),
        (4 * ∑ i ∈ Finset.range (n + 1), e i) / (n + 1 : ℝ)) =
      4 * ∑ i ∈ Finset.range (n + 1), e i := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    simpa only [mul_comm] using
      div_mul_cancel₀ (4 * ∑ i ∈ Finset.range (n + 1), e i) hn
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le
    (show (Finset.range (n + 1)).Nonempty from ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩)
    (hsum.trans_eq hconstant.symm)
  exact ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), hle⟩

theorem sq_le_half_sq_add_two_mul_of_le_half_add_sqrt
    {u v e : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (he : 0 ≤ e)
    (h : v ≤ u / 2 + Real.sqrt e) :
    v ^ 2 ≤ u ^ 2 / 2 + 2 * e := by
  have hright : 0 ≤ u / 2 + Real.sqrt e :=
    add_nonneg (div_nonneg hu (by norm_num)) (Real.sqrt_nonneg _)
  have hsquare : v ^ 2 ≤ (u / 2 + Real.sqrt e) ^ 2 :=
    (sq_le_sq₀ hv hright).mpr h
  nlinarith only [hsquare, Real.sq_sqrt he, sq_nonneg (u / 2 - Real.sqrt e)]

theorem exists_sq_le_four_mul_sum_div_of_le_half_add_sqrt
    (u e : ℕ → ℝ) (n : ℕ)
    (hu : ∀ j ≤ n, 0 ≤ u j) (he : ∀ j ≤ n, 0 ≤ e j)
    (hinit : u 0 ^ 2 ≤ e 0)
    (hrec : ∀ j < n, u (j + 1) ≤ u j / 2 + Real.sqrt (e (j + 1))) :
    ∃ j ≤ n, u j ^ 2 ≤
      (4 * ∑ i ∈ Finset.range (n + 1), e i) / (n + 1 : ℝ) := by
  apply exists_sq_le_four_mul_sum_div_of_sq_le_half_add u e n hinit
  intro j hj
  exact sq_le_half_sq_add_two_mul_of_le_half_add_sqrt
    (hu j hj.le) (hu (j + 1) (Nat.succ_le_of_lt hj))
    (he (j + 1) (Nat.succ_le_of_lt hj)) (hrec j hj)

theorem exists_sq_div_pow_four_le_of_increment_le
    (d e : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n, 0 ≤ d j) (he : ∀ j ≤ n, 0 ≤ e j)
    (hinit : d 0 ^ 2 ≤ e 0)
    (hinc : ∀ j < n, d (j + 1) ≤
      d j + (2 : ℝ) ^ (j + 1) * Real.sqrt (e (j + 1))) :
    ∃ j ≤ n, d j ^ 2 / (4 : ℝ) ^ j ≤
      (4 * ∑ i ∈ Finset.range (n + 1), e i) / (n + 1 : ℝ) := by
  let u : ℕ → ℝ := fun j => d j / (2 : ℝ) ^ j
  have hu : ∀ j ≤ n, 0 ≤ u j := fun j hj =>
    div_nonneg (hd j hj) (pow_nonneg (by norm_num) j)
  have hrec : ∀ j < n, u (j + 1) ≤ u j / 2 + Real.sqrt (e (j + 1)) := by
    intro j hj
    have htwo : (2 : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h := div_le_div_of_nonneg_right (hinc j hj)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (j + 1))
    change d (j + 1) / (2 : ℝ) ^ (j + 1) ≤ _
    refine h.trans_eq ?_
    rw [add_div, mul_div_cancel_left₀ _ htwo]
    dsimp only [u]
    rw [pow_succ, div_div]
  obtain ⟨j, hj, hbound⟩ := exists_sq_le_four_mul_sum_div_of_le_half_add_sqrt
    u e n hu he (by simpa only [u, pow_zero, div_one] using hinit) hrec
  refine ⟨j, hj, ?_⟩
  have hpower : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simpa only [u, div_pow, hpower] using hbound

theorem exists_sq_div_pow_four_le_of_sqrt_increment_le
    (d e : ℕ → ℝ) (n : ℕ)
    (hd : ∀ j ≤ n, 0 ≤ d j) (he : ∀ j ≤ n, 0 ≤ e j)
    (hinit : d 0 ^ 2 ≤ e 0)
    (hinc : ∀ j < n, d (j + 1) ≤ d j +
      Real.sqrt (((4 : ℝ) ^ (j + 1) - (4 : ℝ) ^ j) * e (j + 1))) :
    ∃ j ≤ n, d j ^ 2 / (4 : ℝ) ^ j ≤
      (4 * ∑ i ∈ Finset.range (n + 1), e i) / (n + 1 : ℝ) := by
  apply exists_sq_div_pow_four_le_of_increment_le d e n hd he hinit
  intro j hj
  apply (hinc j hj).trans
  apply add_le_add_right
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _), ?_⟩
  have hej : 0 ≤ e (j + 1) := he (j + 1) (Nat.succ_le_of_lt hj)
  have hpower : ((2 : ℝ) ^ (j + 1)) ^ 2 = (4 : ℝ) ^ (j + 1) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hpower, Real.sq_sqrt hej]
  exact mul_le_mul_of_nonneg_right
    (sub_le_self _ (pow_nonneg (by norm_num) j)) hej

end DifferentialGeometry.Analysis
