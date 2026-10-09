import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

def diagonalMatrixRank (t : ℝ) : ℕ :=
  (Matrix.diagonal (fun i : Fin 3 => if i = (0 : Fin 3) then (1 : ℝ) else t)).rank

theorem diagonalMatrixRank_zero : diagonalMatrixRank 0 = 1 := by
  rw [diagonalMatrixRank, Matrix.rank_diagonal]
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter
      (fun x : Fin 3 => (if x = (0 : Fin 3) then (1 : ℝ) else 0) ≠ 0)) =
      {(0 : Fin 3)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hx
      simp [hx] at h
    · intro hx
      subst hx
      simp
  rw [hf, Finset.card_singleton]

theorem diagonalMatrixRank_of_ne_zero {t : ℝ} (ht : t ≠ 0) : diagonalMatrixRank t = 3 := by
  rw [diagonalMatrixRank, Matrix.rank_diagonal]
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter
      (fun x : Fin 3 => ¬(if x = (0 : Fin 3) then (1 : ℝ) else t) = 0)) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _
    by_cases hx : x = (0 : Fin 3)
    · simp [hx]
    · simp [hx, ht]
  rw [hf, Finset.card_univ, Fintype.card_fin]

theorem diagonalMatrixRank_ne_two (t : ℝ) : diagonalMatrixRank t ≠ 2 := by
  rcases eq_or_ne t 0 with h | h
  · rw [h, diagonalMatrixRank_zero]
    norm_num
  · rw [diagonalMatrixRank_of_ne_zero h]
    norm_num

theorem pointwise_rank_ne_two_not_constant :
    (∀ t : ℝ, diagonalMatrixRank t ≠ 2) ∧
      ¬ ∃ q : ℕ, ∀ t : ℝ, diagonalMatrixRank t = q := by
  refine ⟨diagonalMatrixRank_ne_two, ?_⟩
  rintro ⟨q, hq⟩
  have h1 : q = 1 := by
    have h := hq 0
    rw [diagonalMatrixRank_zero] at h
    omega
  have h3 : q = 3 := by
    have h := hq 1
    rw [diagonalMatrixRank_of_ne_zero one_ne_zero] at h
    omega
  omega

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
