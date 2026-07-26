import Mathlib

set_option autoImplicit false

/-!
# Dyadic scale selection

This file contains the scalar first-crossing argument used to select a scale
with controlled doubling from a normalized-volume threshold.
-/

namespace DifferentialGeometry.Analysis.Calculus

/-- A nonnegative sequence with a positive eventual lower bound cannot keep
dropping by a fixed factor `q < 1`.  At the first failure of that geometric
drop, its value is still no larger than the initial value. -/
theorem exists_drop_lower
    (W : ℕ → ℝ) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : ∀ j : ℕ, 0 ≤ W j) (hε : 0 < ε)
    (hlow : ∀ᶠ j : ℕ in Filter.atTop, ε ≤ W j) :
    ∃ j : ℕ, q * W j < W (j + 1) ∧ W j ≤ W 0 := by
  classical
  have hex : ∃ j : ℕ, q * W j < W (j + 1) := by
    by_contra hnone
    push Not at hnone
    have hbound : ∀ j : ℕ, W j ≤ q ^ j * W 0 := by
      intro j
      induction j with
      | zero =>
          simpa only [pow_zero, one_mul] using (le_refl (W 0))
      | succ j ih =>
          calc
            W (j + 1) ≤ q * W j := hnone j
            _ ≤ q * (q ^ j * W 0) := mul_le_mul_of_nonneg_left ih hq0
            _ = q ^ (j + 1) * W 0 := by rw [pow_succ]; ring
    have htend : Filter.Tendsto (fun j : ℕ => q ^ j * W 0)
        Filter.atTop (nhds 0) :=
      by simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (W 0)
    have hsmall : ∀ᶠ j : ℕ in Filter.atTop, q ^ j * W 0 < ε :=
      htend.eventually_lt_const hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlow.and hsmall)
    obtain ⟨hNlow, hNsmall⟩ := hN N le_rfl
    exact (not_lt_of_ge hNlow) (lt_of_le_of_lt (hbound N) hNsmall)
  let j : ℕ := Nat.find hex
  have hj : q * W j < W (j + 1) := Nat.find_spec hex
  have hprefix : ∀ k : ℕ, k ≤ j → W k ≤ W 0 := by
    intro k
    induction k with
    | zero => exact fun _ => le_rfl
    | succ k ih =>
        intro hk
        have hkj : k < j := Nat.lt_of_succ_le hk
        have hnot : ¬q * W k < W (k + 1) := Nat.find_min hex hkj
        have hstep : W (k + 1) ≤ W k := by
          calc
            W (k + 1) ≤ q * W k := le_of_not_gt hnot
            _ ≤ W k := by
              exact mul_le_of_le_one_left (hW k) (le_of_lt hq1)
        exact hstep.trans (ih (Nat.le_trans (Nat.le_succ k) hk))
  exact ⟨j, hj, hprefix j le_rfl⟩

/-- If a real sequence crosses a scaled threshold, and consecutive threshold
scales differ by a nonnegative factor `c`, then immediately before its first
crossing the sequence has ratio strictly smaller than `c`. -/
theorem exists_ratio_cross
    (V a : ℕ → ℝ) {κ c : ℝ} (hc : 0 ≤ c)
    (hscale : ∀ j : ℕ, a j = c * a (j + 1))
    (hzero : V 0 < κ * a 0)
    (hhit : ∃ N : ℕ, κ * a N ≤ V N) :
    ∃ j : ℕ, V j < c * V (j + 1) := by
  classical
  let P : ℕ → Prop := fun j => κ * a j ≤ V j
  have hP : ∃ N : ℕ, P N := hhit
  let N : ℕ := Nat.find hP
  have hN : P N := Nat.find_spec hP
  have hN_ne : N ≠ 0 := by
    intro hN0
    have hN' : P 0 := by simpa only [hN0] using hN
    exact (not_le_of_gt hzero) hN'
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_ne
  let j : ℕ := N - 1
  have hjN : j + 1 = N := by
    dsimp only [j]
    omega
  have hjlt : j < N := by omega
  have hj : ¬P j := Nat.find_min hP hjlt
  refine ⟨j, ?_⟩
  have hjlt' : V j < κ * a j := lt_of_not_ge hj
  calc
    V j < κ * a j := hjlt'
    _ = c * (κ * a (j + 1)) := by rw [hscale]; ring
    _ ≤ c * V (j + 1) := mul_le_mul_of_nonneg_left (by simpa only [hjN] using hN) hc

/-- A dyadic normalized-volume threshold crossing selects a scale whose outer
value is strictly less than `2^n` times the next, half-scale value. -/
theorem exists_dyadic_scale
    (V : ℕ → ℝ) (n : ℕ) {κ r : ℝ}
    (hzero : V 0 < κ * r ^ n)
    (hhit : ∃ N : ℕ, κ * (r / (2 : ℝ) ^ N) ^ n ≤ V N) :
    ∃ j : ℕ, V j < (2 : ℝ) ^ n * V (j + 1) := by
  let a : ℕ → ℝ := fun j => (r / (2 : ℝ) ^ j) ^ n
  apply exists_ratio_cross V a (κ := κ) (c := (2 : ℝ) ^ n) (by positivity)
  · intro j
    dsimp only [a]
    rw [div_pow, div_pow]
    field_simp
    rw [pow_add, mul_pow]
    norm_num
    ring
  · simpa only [a, pow_zero, div_one] using hzero
  · simpa only [a] using hhit

end DifferentialGeometry.Analysis.Calculus
