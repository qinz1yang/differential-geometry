import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
The characteristic polynomial of a real oriented orthogonal three-matrix is determined by
its trace. Its inverse is its transpose, so characteristic-polynomial reversal fixes the
middle coefficients. Cayley–Hamilton gives actual third, fourth and sixth powers in the
three interior integral trace cases, without a finite-order or classification premise.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace DifferentialGeometry.Geometry.FlatSurface

theorem orthogonal_charpoly_cubic (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C A.trace * X - 1 := by
  have hU : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (hd ▸ isUnit_one)
  have hr : A.charpoly = -A.charpoly.reverse := by
    have hi := Matrix.charpoly_inv A hU
    rw [Matrix.inv_eq_left_inv ho, Matrix.charpoly_transpose, ← Matrix.reverse_charpoly] at hi
    simpa [hd, pow_succ] using hi
  have h0 : A.charpoly.coeff 0 = -1 := by
    have hc := Matrix.det_eq_sign_charpoly_coeff A
    norm_num [hd] at hc
    linarith
  have h2 : A.charpoly.coeff 2 = -A.trace := by
    have hc := Matrix.trace_eq_neg_charpoly_coeff A
    norm_num at hc
    linarith
  have h1 : A.charpoly.coeff 1 = A.trace := by
    have hc := congrArg (fun p : ℝ[X] => p.coeff 1) hr
    simp only [coeff_neg, coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, revAt, Function.Embedding.coeFn_mk] at hc
    norm_num at hc
    rw [h2, neg_neg] at hc
    exact hc
  have h3 : A.charpoly.coeff 3 = 1 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      (Matrix.charpoly_monic A).coeff_natDegree
  apply (Polynomial.ext_iff_natDegree_le (n := 3) (by simp) (by compute_degree)).mpr
  intro i hi
  interval_cases i <;> simp [h0, h1, h2, h3, coeff_one]

theorem orthogonal_trace_zero_pow (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (ht : A.trace = 0) : A ^ 3 = 1 := by
  have hp := orthogonal_charpoly_cubic A ho hd
  rw [ht] at hp
  have ha := Matrix.aeval_self_charpoly A
  rw [hp] at ha
  exact sub_eq_zero.mp (by simpa using ha)

theorem orthogonal_trace_one_pow (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (ht : A.trace = 1) : A ^ 4 = 1 := by
  have hp : (X + 1) * A.charpoly = X ^ 4 - 1 := by
    rw [orthogonal_charpoly_cubic A ho hd, ht]
    simp only [map_one]
    ring
  have ha : aeval A ((X + 1) * A.charpoly) = 0 := by
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
  rw [hp] at ha
  exact sub_eq_zero.mp (by simpa using ha)

theorem orthogonal_trace_two_pow (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (ht : A.trace = 2) : A ^ 6 = 1 := by
  have hp : ((X + 1) * (X ^ 2 + X + 1)) * A.charpoly = X ^ 6 - 1 := by
    rw [orthogonal_charpoly_cubic A ho hd, ht]
    simp only [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]
    ring
  have ha : aeval A (((X + 1) * (X ^ 2 + X + 1)) * A.charpoly) = 0 := by
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
  rw [hp] at ha
  exact sub_eq_zero.mp (by simpa using ha)

end DifferentialGeometry.Geometry.FlatSurface
