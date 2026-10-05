import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalCubic

/-!
A real orthogonal three-matrix of maximum trace is the identity, by its unit columns.
At trace minus one its oriented cubic makes the square-minus-identity nilpotent; zero
nilpotent trace and orthogonality then force the square to be the identity. No finite
order or diagonalization premise is supplied.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace DifferentialGeometry.Geometry.FlatSurface

theorem orthogonal_trace_three_eq_one (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (ht : A.trace = 3) : A = 1 := by
  classical
  have hcols (j : Fin 3) : ∑ k, A k j ^ 2 = 1 := by
    have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j j) ho
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      ite_true, pow_two] using hc
  have hdiag (j : Fin 3) : A j j ≤ 1 := by
    have hs : A j j ^ 2 ≤ 1 := by
      rw [← hcols j]
      exact Finset.single_le_sum (fun k hk => sq_nonneg (A k j)) (Finset.mem_univ j)
    exact (le_abs_self (A j j)).trans ((sq_le_one_iff_abs_le_one (A j j)).mp hs)
  have hsum : ∑ k, (1 - A k k) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    change 3 - A.trace = 0
    rw [ht]
    ring
  have hdiagOne (j : Fin 3) : A j j = 1 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (by intro k hk; exact sub_nonneg.mpr (hdiag k))).mp hsum j (Finset.mem_univ j)
    linarith
  have hoff (i j : Fin 3) (hij : i ≠ j) : A i j = 0 := by
    have hmerge := Finset.sum_erase_add Finset.univ (fun k => A k j ^ 2)
      (Finset.mem_univ j)
    rw [hcols j, hdiagOne j] at hmerge
    have he : ∑ k ∈ Finset.univ.erase j, A k j ^ 2 = 0 := by simp only [one_pow] at hmerge; linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (by intro k hk; exact sq_nonneg (A k j))).mp he i
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    exact sq_eq_zero_iff.mp hz
  ext i j
  by_cases hij : i = j
  · subst i
    simpa only [Matrix.one_apply, ite_true] using hdiagOne j
  · simp only [Matrix.one_apply, hij, ite_false]
    exact hoff i j hij

theorem orthogonal_trace_neg_one_sq (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (ht : A.trace = -1) : A ^ 2 = 1 := by
  have hp : (X - 1) * A.charpoly = (X ^ 2 - 1) ^ 2 := by
    rw [orthogonal_charpoly_cubic A ho hd, ht]
    simp only [map_neg, map_one]
    ring
  have ha : aeval A ((X - 1) * A.charpoly) = 0 := by
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
  rw [hp] at ha
  have hn : IsNilpotent (A ^ 2 - 1) := ⟨2, by simpa using ha⟩
  have hz : (A ^ 2 - 1).trace = 0 :=
    isNilpotent_iff_eq_zero.mp (Matrix.isNilpotent_trace_of_isNilpotent hn)
  rw [Matrix.trace_sub, Matrix.trace_one] at hz
  have ht2 : (A ^ 2).trace = 3 := by norm_num at hz; linarith
  have ho2 : (A ^ 2).transpose * A ^ 2 = 1 := by
    simp only [pow_two, Matrix.transpose_mul]
    calc
      A.transpose * A.transpose * (A * A) = (A.transpose * (A.transpose * A)) * A :=
        by simp only [mul_assoc]
      _ = 1 := by rw [ho, mul_one, ho]
  exact orthogonal_trace_three_eq_one (A ^ 2) ho2 ht2

end DifferentialGeometry.Geometry.FlatSurface
