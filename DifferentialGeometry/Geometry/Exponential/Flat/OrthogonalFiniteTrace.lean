import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalCubic

/-!
A nonidentity oriented orthogonal involution in dimension three has trace minus one.
For any finite orthogonal representation, averaging its actual matrices has nonnegative
trace: the square norm of the average is its cardinal multiple. These kernels bound an
actual involutive three-dimensional point group without a classification premise.
-/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

theorem orthogonal_nontrivial_involution_trace (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (hp : A ^ 2 = 1) (hne : A ≠ 1) :
    A.trace = -1 := by
  have hc : A ^ 3 = A := by rw [pow_succ, hp, one_mul]
  have ha := Matrix.aeval_self_charpoly A
  rw [orthogonal_charpoly_cubic A ho hd] at ha
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one,
    hc, hp, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_one] at ha
  have hz : (A.trace + 1) • (A - 1) = 0 := by
    calc
      (A.trace + 1) • (A - 1) = A - A.trace • 1 + A.trace • A - 1 := by module
      _ = 0 := ha
  rcases smul_eq_zero.mp hz with h | h
  · linarith
  · exact False.elim (hne (sub_eq_zero.mp h))

theorem finite_orthogonal_trace_sum_nonneg {K : Type*} [instGroup : Group K]
    [instFinite : Fintype K] (rho : K →* Matrix (Fin 3) (Fin 3) ℝ)
    (ho : ∀ g, (rho g).transpose * rho g = 1) : 0 ≤ ∑ g : K, (rho g).trace := by
  let S : Matrix (Fin 3) (Fin 3) ℝ := ∑ g : K, rho g
  have hleft (g : K) : (rho g).transpose * S = S := by
    have hi : (rho g).transpose = rho g⁻¹ :=
      Matrix.left_inv_eq_left_inv (ho g) (by rw [← map_mul, inv_mul_cancel, map_one])
    rw [hi]
    change rho g⁻¹ * (∑ h : K, rho h) = _
    rw [Finset.mul_sum]
    simp_rw [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (by intro h; rfl)
  have hS : S.transpose * S = (Fintype.card K : ℝ) • S := by
    change (∑ g : K, rho g).transpose * S = _
    rw [Matrix.transpose_sum, Finset.sum_mul]
    simp_rw [hleft]
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hnonneg : 0 ≤ (S.transpose * S).trace := by
    change 0 ≤ ∑ j : Fin 3, (S.transpose * S) j j
    apply Finset.sum_nonneg
    intro j hj
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    exact Finset.sum_nonneg (fun i hi => mul_self_nonneg (S i j))
  rw [hS, Matrix.trace_smul, smul_eq_mul] at hnonneg
  have hcard : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos (α := K)
  have htrace : 0 ≤ S.trace := (mul_nonneg_iff_of_pos_left hcard).mp hnonneg
  simpa only [S, Matrix.trace_sum] using htrace

end DifferentialGeometry.Geometry.FlatSurface
