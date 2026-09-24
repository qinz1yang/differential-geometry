import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace DifferentialGeometry.Analysis

theorem exp_mul_add_sum_le_of_successive_debits
    {n : ℕ} (time volume : Fin (n + 1) → ℝ) (debit : Fin n → ℝ) (K : ℝ)
    (hstep : ∀ i : Fin n, volume i.succ + debit i ≤
      Real.exp (K * (time i.succ - time i.castSucc)) * volume i.castSucc) :
    Real.exp (-K * time (Fin.last n)) * volume (Fin.last n) +
      ∑ i : Fin n, Real.exp (-K * time i.succ) * debit i ≤
        Real.exp (-K * time 0) * volume 0 := by
  have htelescope : ∀ m : ℕ, ∀ z : Fin (m + 1) → ℝ, ∀ d : Fin m → ℝ,
      (∀ i, z i.succ + d i ≤ z i.castSucc) →
      z (Fin.last m) + ∑ i : Fin m, d i ≤ z 0 := by
    intro m
    induction m with
    | zero => intro z d h; simp
    | succ m ih =>
      intro z d h
      have hp := ih (fun i => z i.castSucc) (fun i => d i.castSucc)
        (fun i => h i.castSucc)
      have hl := h (Fin.last m)
      rw [Fin.sum_univ_castSucc]
      change z (Fin.last m).castSucc + ∑ i : Fin m, d i.castSucc ≤ z 0 at hp
      change z (Fin.last (m + 1)) + d (Fin.last m) ≤ z (Fin.last m).castSucc at hl
      linarith
  let z := fun i => Real.exp (-K * time i) * volume i
  let d := fun i : Fin n => Real.exp (-K * time i.succ) * debit i
  have hweighted : ∀ i : Fin n, z i.succ + d i ≤ z i.castSucc := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hstep i) (Real.exp_pos (-K * time i.succ)).le
    have he : Real.exp (-K * time i.succ) *
        Real.exp (K * (time i.succ - time i.castSucc)) = Real.exp (-K * time i.castSucc) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [z, d]
    rw [mul_add, ← mul_assoc, he] at h
    exact h
  exact htelescope n z d hweighted

theorem sum_le_exp_mul_of_successive_debits
    {n : ℕ} (time volume : Fin (n + 1) → ℝ) (debit : Fin n → ℝ)
    {K T : ℝ} (hK : 0 ≤ K)
    (hT : ∀ i : Fin n, time i.succ ≤ T) (hvol : 0 ≤ volume (Fin.last n))
    (hdebit : ∀ i, 0 ≤ debit i)
    (hstep : ∀ i : Fin n, volume i.succ + debit i ≤
      Real.exp (K * (time i.succ - time i.castSucc)) * volume i.castSucc) :
    ∑ i : Fin n, debit i ≤ Real.exp (K * (T - time 0)) * volume 0 := by
  let z := fun i => Real.exp (-K * time i) * volume i
  let d := fun i : Fin n => Real.exp (-K * time i.succ) * debit i
  have hsum := exp_mul_add_sum_le_of_successive_debits time volume debit K hstep
  have hzlast : 0 ≤ z (Fin.last n) := mul_nonneg (Real.exp_pos _).le hvol
  have hlower : Real.exp (-K * T) * (∑ i : Fin n, debit i) ≤ ∑ i : Fin n, d i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hdebit i)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hT i) (neg_nonpos.mpr hK))
  have hbound : Real.exp (-K * T) * (∑ i : Fin n, debit i) ≤
      Real.exp (-K * time 0) * volume 0 := by
    change z (Fin.last n) + ∑ i : Fin n, d i ≤
      Real.exp (-K * time 0) * volume 0 at hsum
    linarith
  have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (K * T)).le
  have he : Real.exp (K * T) * Real.exp (-K * T) = 1 := by
    rw [← Real.exp_add]
    simp
  have hstart : Real.exp (K * T) * Real.exp (-K * time 0) =
      Real.exp (K * (T - time 0)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc, he, one_mul, hstart] using h

end DifferentialGeometry.Analysis
