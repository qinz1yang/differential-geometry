import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace LinearMap.BilinForm

theorem det_toMatrix_basis_change
    {R E i : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype i] [DecidableEq i] (B : LinearMap.BilinForm R E) (b c : Module.Basis i R E) :
    (toMatrix c B).det = b.det c ^ 2 * (toMatrix b B).det := by
  rw [← B.toMatrix_mul_basis_toMatrix b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Module.Basis.det_apply]
  ring

theorem det_gram_cons_eq_mul_of_orthogonal
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {n : Nat} (B : LinearMap.BilinForm R V) (e : V) (v : Fin n → V) (c : Fin n → R)
    (horth : ∀ i, B ((∑ j, c j • v j) - e) (v i) = 0) :
    (Matrix.of fun i j : Fin (n + 1) =>
      B (Fin.cons (α := fun _ => V) e v i) (Fin.cons (α := fun _ => V) e v j)).det =
      B ((∑ j, c j • v j) - e) ((∑ j, c j • v j) - e) *
        (Matrix.of fun i j => B (v i) (v j)).det := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun i j => B (Fin.cons (α := fun _ => V) e v i) (Fin.cons (α := fun _ => V) e v j)
  let w := (∑ j, c j • v j) - e
  have hrow : (fun j => B w (Fin.cons (α := fun _ => V) e v j)) =
      fun j => ∑ i, Fin.cons (α := fun _ => R) (-1) c i • A i j := by
    funext j
    simp only [w, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, A, Matrix.of_apply,
      neg_smul, one_smul]
    rw [sub_eq_add_neg, add_comm]
  have hdet : (A.updateRow 0 (fun j => B w (Fin.cons (α := fun _ => V) e v j))).det = -A.det := by
    rw [hrow]
    convert Matrix.det_updateRow_sum A 0 (Fin.cons (α := fun _ => R) (-1) c) using 1
    · congr 2
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply]
    · simp
  have hwe : B w e = -B w w := by
    have hww : B w w = -B w e := by
      change B w ((∑ j, c j • v j) - e) = _
      rw [map_sub, map_sum]
      simp only [map_smul, smul_eq_mul, show ∀ i, B w (v i) = 0 from horth,
        mul_zero, Finset.sum_const_zero, zero_sub]
    rw [hww, neg_neg]
  have hexpand : (A.updateRow 0 (fun j => B w (Fin.cons (α := fun _ => V) e v j))).det =
      -B w w * (Matrix.of fun i j => B (v i) (v j)).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have htail : (A.updateRow 0 (fun j => B w (Fin.cons (α := fun _ => V) e v j))).submatrix
        Fin.succ (Fin.succAbove 0) = Matrix.of fun i j => B (v i) (v j) := by
      ext i j
      simp [A]
    simp only [Matrix.updateRow_self, Fin.cons_zero, Fin.cons_succ, hwe,
      show ∀ i, B w (v i) = 0 from horth,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
    rw [htail]
  rw [hdet] at hexpand
  exact neg_injective (by simpa only [neg_mul] using hexpand)

end LinearMap.BilinForm
