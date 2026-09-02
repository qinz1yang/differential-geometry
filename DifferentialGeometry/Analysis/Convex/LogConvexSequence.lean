import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis.Convex

private lemma logConvex_single_step {f : ℕ → ℝ} (hnn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k) :
    ∀ b a : ℕ, a ≤ b → f (a + 1) * f b ≤ f a * f (b + 1) := by
  intro b
  induction b with
  | zero =>
    intro a ha
    have ha0 : a = 0 := Nat.le_zero.mp ha
    subst ha0
    exact le_of_eq (mul_comm _ _)
  | succ b' ih =>
    intro a ha
    rcases eq_or_lt_of_le ha with heq | hlt
    · subst heq
      exact le_of_eq (mul_comm _ _)
    · have ha' : a ≤ b' := Nat.lt_succ_iff.mp hlt
      have hIH := ih a ha'
      have hlcb := hlc b'
      change f (a + 1) * f (b' + 1) ≤ f a * f (b' + 2)
      have hprod : f (a + 1) * f (b' + 1) * f b' ≤ f a * f (b' + 2) * f b' := by
        calc f (a + 1) * f (b' + 1) * f b'
            = (f (a + 1) * f b') * f (b' + 1) := by ring
          _ ≤ (f a * f (b' + 1)) * f (b' + 1) :=
            mul_le_mul_of_nonneg_right hIH (hnn (b' + 1))
          _ = f a * f (b' + 1) ^ 2 := by ring
          _ ≤ f a * (f (b' + 2) * f b') := mul_le_mul_of_nonneg_left hlcb (hnn a)
          _ = f a * f (b' + 2) * f b' := by ring
      rcases eq_or_lt_of_le (hnn b') with hzero | hpos
      · have hb1sq : f (b' + 1) ^ 2 ≤ 0 := by
          have h := hlcb
          rw [← hzero, mul_zero] at h
          exact h
        have hb1 : f (b' + 1) = 0 := by
          nlinarith [sq_nonneg (f (b' + 1)), hb1sq]
        rw [hb1, mul_zero]
        exact mul_nonneg (hnn a) (hnn (b' + 2))
      · nlinarith [hprod, hpos]

private lemma logConvex_extreme_pair_add {f : ℕ → ℝ} (hnn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k) :
    ∀ (e a' j : ℕ), f (a' + e) * f (a' + e + j) ≤ f a' * f (a' + 2 * e + j) := by
  intro e
  induction e with
  | zero =>
    intro a' j
    simp
  | succ e' ih =>
    intro a' j
    have hIH := ih (a' + 1) j
    have hss := logConvex_single_step hnn hlc (a' + 2 * e' + 1 + j) a' (by omega)
    have hi1 : a' + 1 + e' = a' + (e' + 1) := by omega
    have hi3 : a' + 1 + 2 * e' + j = a' + 2 * e' + 1 + j := by omega
    have hi4 : a' + 2 * e' + 1 + j + 1 = a' + 2 * (e' + 1) + j := by omega
    rw [hi1, hi3] at hIH
    rw [hi4] at hss
    exact le_trans hIH hss

theorem logConvex_extreme_pair {f : ℕ → ℝ} (hnn : ∀ k, 0 ≤ f k)
    (hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k)
    {σ₁ σ₂ τ₁ τ₂ : ℕ} (h1 : τ₁ ≤ σ₁) (h2 : σ₁ ≤ σ₂)
    (hsum : τ₁ + τ₂ = σ₁ + σ₂) :
    f σ₁ * f σ₂ ≤ f τ₁ * f τ₂ := by
  have key := logConvex_extreme_pair_add hnn hlc (σ₁ - τ₁) τ₁ (σ₂ - σ₁)
  have e1 : σ₁ = τ₁ + (σ₁ - τ₁) := by omega
  have e2 : σ₂ = τ₁ + (σ₁ - τ₁) + (σ₂ - σ₁) := by omega
  have e3 : τ₂ = τ₁ + 2 * (σ₁ - τ₁) + (σ₂ - σ₁) := by omega
  rw [e1, e2, e3]
  exact key

end DifferentialGeometry.Analysis.Convex
