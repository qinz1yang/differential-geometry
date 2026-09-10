import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Poincare.Geometry.Affine

def lineAffineAlignment (s c : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 =>
    let A := lineAffineAlignment s c n
    (A.1 * s n, A.2 - A.1 * s n * c n)

theorem lineAffineAlignment_sign (s c : ℕ → ℝ)
    (hs : ∀ n, s n = 1 ∨ s n = -1) (n : ℕ) :
    (lineAffineAlignment s c n).1 = 1 ∨ (lineAffineAlignment s c n).1 = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with ih | ih <;> rcases hs n with hn | hn <;>
      simp [lineAffineAlignment, ih, hn]

theorem lineAffineAlignment_transition_error (s c : ℕ → ℝ) (n : ℕ)
    (hs : (s n) ^ 2 = 1) (x y : ℝ) :
    ((lineAffineAlignment s c (n + 1)).1 * y + (lineAffineAlignment s c (n + 1)).2) -
      ((lineAffineAlignment s c n).1 * x + (lineAffineAlignment s c n).2) =
      (lineAffineAlignment s c (n + 1)).1 * (y - (s n * x + c n)) := by
  simp only [lineAffineAlignment]
  ring_nf
  rw [hs]
  ring

theorem abs_lineAffineAlignment_transition_error (s c : ℕ → ℝ)
    (hs : ∀ n, s n = 1 ∨ s n = -1) (n : ℕ) (x y : ℝ) :
    |((lineAffineAlignment s c (n + 1)).1 * y + (lineAffineAlignment s c (n + 1)).2) -
      ((lineAffineAlignment s c n).1 * x + (lineAffineAlignment s c n).2)| =
      |y - (s n * x + c n)| := by
  have hs' : (s n) ^ 2 = 1 := by rcases hs n with h | h <;> simp [h]
  rw [lineAffineAlignment_transition_error s c n hs', abs_mul]
  rcases lineAffineAlignment_sign s c hs (n + 1) with h | h <;> simp [h]

end Poincare.Geometry.Affine
