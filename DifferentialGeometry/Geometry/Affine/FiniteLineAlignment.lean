import DifferentialGeometry.Geometry.Affine.LineAlignment
import Mathlib.Algebra.Module.Defs

namespace DifferentialGeometry.Geometry.Affine

def finiteLineAffineAlignment {n : ℕ} (s c : Fin n → ℝ) (i : Fin (n + 1)) : ℝ × ℝ :=
  lineAffineAlignment (fun j ↦ if h : j < n then s ⟨j, h⟩ else 1)
    (fun j ↦ if h : j < n then c ⟨j, h⟩ else 0) i.val

theorem finiteLineAffineAlignment_zero {n : ℕ} (s c : Fin n → ℝ) :
    finiteLineAffineAlignment s c 0 = (1, 0) := rfl

theorem finiteLineAffineAlignment_succ {n : ℕ} (s c : Fin n → ℝ) (j : Fin n) :
    finiteLineAffineAlignment s c j.succ =
      ((finiteLineAffineAlignment s c j.castSucc).1 * s j,
        (finiteLineAffineAlignment s c j.castSucc).2 -
          (finiteLineAffineAlignment s c j.castSucc).1 * s j * c j) := by
  simp only [finiteLineAffineAlignment, Fin.val_succ, Fin.val_castSucc,
    lineAffineAlignment, dif_pos j.isLt]

theorem finiteLineAffineAlignment_sign {n : ℕ} (s c : Fin n → ℝ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (i : Fin (n + 1)) :
    (finiteLineAffineAlignment s c i).1 = 1 ∨ (finiteLineAffineAlignment s c i).1 = -1 := by
  apply lineAffineAlignment_sign
  intro j
  split_ifs with hj
  · exact hs ⟨j, hj⟩
  · exact Or.inl rfl

theorem abs_finiteLineAffineAlignment_transition_error {n : ℕ} (s c : Fin n → ℝ)
    (hs : ∀ j, s j = 1 ∨ s j = -1) (j : Fin n) (x y : ℝ) :
    |(finiteLineAffineAlignment s c j.succ).1 * y + (finiteLineAffineAlignment s c j.succ).2 -
      ((finiteLineAffineAlignment s c j.castSucc).1 * x + (finiteLineAffineAlignment s c j.castSucc).2)| =
      |y - (s j * x + c j)| := by
  have h := abs_lineAffineAlignment_transition_error
    (fun k ↦ if hk : k < n then s ⟨k, hk⟩ else 1)
    (fun k ↦ if hk : k < n then c ⟨k, hk⟩ else 0)
    (by
      intro k
      split_ifs with hk
      · exact hs ⟨k, hk⟩
      · exact Or.inl rfl) j.val x y
  simpa only [finiteLineAffineAlignment, Fin.val_succ, Fin.val_castSucc, dif_pos j.isLt] using h

theorem finiteLineAffineAlignment_smul_eq {n : ℕ} (s c : Fin n → ℝ)
    (j : Fin n) (hs : s j = 1 ∨ s j = -1)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (v w : V) (hw : w = s j • v) :
    (finiteLineAffineAlignment s c j.succ).1 • w =
      (finiteLineAffineAlignment s c j.castSucc).1 • v := by
  rw [finiteLineAffineAlignment_succ, hw, smul_smul]
  change ((finiteLineAffineAlignment s c j.castSucc).1 * s j * s j) • v = _
  have hs' : s j * s j = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  rw [mul_assoc, hs', mul_one]

end DifferentialGeometry.Geometry.Affine
