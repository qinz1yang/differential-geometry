import DifferentialGeometry.Geometry.Exponential.Flat.OrthogonalCubic

/-!
A nonidentity oriented orthogonal three-matrix whose cube is the identity has trace zero.
Its cubic relation and invertibility exclude an idempotent nonidentity matrix. Its square
is its transpose, so the square has the same zero trace. No eigenbasis is supplied.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace DifferentialGeometry.Geometry.FlatSurface

theorem orthogonal_nontrivial_cube_trace (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hd : A.det = 1) (hp : A ^ 3 = 1) (hne : A ≠ 1) :
    A.trace = 0 := by
  have ha := Matrix.aeval_self_charpoly A
  rw [orthogonal_charpoly_cubic A ho hd] at ha
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one,
    hp, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at ha
  have hz : A.trace • (A - A ^ 2) = 0 := by
    calc
      A.trace • (A - A ^ 2) = 1 - A.trace • A ^ 2 + A.trace • A - 1 := by module
      _ = 0 := ha
  have hn : A - A ^ 2 ≠ 0 := by
    intro he
    have hA : A ^ 2 = A := (sub_eq_zero.mp he).symm
    have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => A.transpose * M) hA
    rw [pow_two, ← mul_assoc, ho, one_mul] at hm
    exact hne hm
  exact (smul_eq_zero.mp hz).resolve_right hn

theorem orthogonal_cube_trace_square (A : Matrix (Fin 3) (Fin 3) ℝ)
    (ho : A.transpose * A = 1) (hp : A ^ 3 = 1) : (A ^ 2).trace = A.trace := by
  have hi : A ^ 2 = A.transpose := Matrix.left_inv_eq_left_inv
    (by rw [← pow_succ, hp]) ho
  rw [hi, Matrix.trace_transpose]

end DifferentialGeometry.Geometry.FlatSurface
