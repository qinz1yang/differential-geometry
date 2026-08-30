import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Reaction
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Analysis.InnerProductSpace
open scoped BigOperators

def curvatureOperatorReaction3
    (A : Matrix (Fin 3) (Fin 3) Real) : Matrix (Fin 3) (Fin 3) Real :=
  A * A + A.adjugate

private lemma diagProduct_erase_curvatureReaction3
    (l1 l2 l3 : Real) (i : Fin 3) :
    (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase i, ![l1, l2, l3] j) =
      (if i = 0 then l2 * l3 else if i = 1 then l1 * l3 else l1 * l2) := by
  fin_cases i
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3),
      ![l1, l2, l3] j) = l2 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (0 : Fin 3) =
        ({1, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3),
      ![l1, l2, l3] j) = l1 * l3
    have hset : (Finset.univ : Finset (Fin 3)).erase (1 : Fin 3) =
        ({0, 2} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp
  · change (∏ j ∈ (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3),
      ![l1, l2, l3] j) = l1 * l2
    have hset : (Finset.univ : Finset (Fin 3)).erase (2 : Fin 3) =
        ({0, 1} : Finset (Fin 3)) := by
      ext j
      fin_cases j <;> simp
    rw [hset]
    simp

theorem curvatureOperatorReaction3_diagonal (l1 l2 l3 : Real) :
    curvatureOperatorReaction3 (Matrix.diagonal ![l1, l2, l3]) =
      Matrix.diagonal
        ![l1 ^ 2 + l2 * l3, l2 ^ 2 + l1 * l3, l3 ^ 2 + l1 * l2] := by
  unfold curvatureOperatorReaction3
  rw [Matrix.adjugate_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply,
      diagProduct_erase_curvatureReaction3] <;> ring

theorem curvatureOperatorReaction3_orthogonal_conj
    (O A : Matrix (Fin 3) (Fin 3) Real) (hO : O * O.transpose = 1) :
    curvatureOperatorReaction3 (O * A * O.transpose) =
      O * curvatureOperatorReaction3 A * O.transpose := by
  unfold curvatureOperatorReaction3
  have hOinv : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  have hsq : (O * A * O.transpose) * (O * A * O.transpose) =
      O * (A * A) * O.transpose := by
    calc
      (O * A * O.transpose) * (O * A * O.transpose) =
          O * A * (O.transpose * O) * A * O.transpose := by
            simp only [Matrix.mul_assoc]
      _ = O * A * A * O.transpose := by
            rw [hOinv]
            simp
      _ = O * (A * A) * O.transpose := by
            simp only [Matrix.mul_assoc]
  have hadj := adjugate_orthogonal_conj O A hO
  rw [hsq, hadj]
  simp only [mul_add, add_mul, Matrix.mul_assoc]

theorem curvatureOperatorReaction3_commute
    (A : Matrix (Fin 3) (Fin 3) Real) :
    Commute A (curvatureOperatorReaction3 A) := by
  change A * curvatureOperatorReaction3 A = curvatureOperatorReaction3 A * A
  unfold curvatureOperatorReaction3
  rw [mul_add, add_mul, Matrix.mul_adjugate, Matrix.adjugate_mul]
  simp [mul_assoc]

theorem curvatureOperatorReaction3_posSemidef
    {A : Matrix (Fin 3) (Fin 3) Real} (hA : A.PosSemidef) :
    (curvatureOperatorReaction3 A).PosSemidef := by
  have hAh : A.IsHermitian := hA.isHermitian
  have hev : ∀ i : Fin 3, 0 ≤ hAh.eigenvalues i := by
    intro i
    exact hA.eigenvalues_nonneg i
  let U : Matrix.unitaryGroup (Fin 3) Real := hAh.eigenvectorUnitary
  let D : Matrix (Fin 3) (Fin 3) Real := Matrix.diagonal (hAh.eigenvalues)
  have hU : (U : Matrix (Fin 3) (Fin 3) Real) *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.prop)
  have hA_repr : A = (U : Matrix (Fin 3) (Fin 3) Real) * D *
      (U : Matrix (Fin 3) (Fin 3) Real).transpose := by
    have hspec := hAh.spectral_theorem
    simpa [U, D, Matrix.star_eq_conjTranspose] using hspec
  rw [hA_repr]
  rw [curvatureOperatorReaction3_orthogonal_conj _ _ hU]
  have hR : (curvatureOperatorReaction3 D).PosSemidef := by
    rw [show D = Matrix.diagonal (hAh.eigenvalues) by rfl]
    let d : Fin 3 → Real := hAh.eigenvalues
    have hd : d = ![d 0, d 1, d 2] := by
      funext i
      fin_cases i <;> rfl
    rw [congrArg Matrix.diagonal hd]
    rw [curvatureOperatorReaction3_diagonal]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hdn : ∀ j : Fin 3, 0 ≤ d j := by
      intro j
      simpa [d] using hev j
    fin_cases i
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 1) (hdn 2))
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 0) (hdn 2))
    · exact add_nonneg (sq_nonneg _) (mul_nonneg (hdn 0) (hdn 1))
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hR
      (U : Matrix (Fin 3) (Fin 3) Real))

theorem curvatureOperatorReaction3_diagonal_rank_two_null_direction
    (a b : Real) :
    curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 = a * b := by
  rw [curvatureOperatorReaction3_diagonal]
  simp [Matrix.diagonal]

theorem curvatureOperatorReaction3_diagonal_rank_two_null_direction_pos
    {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    0 < curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 := by
  rw [curvatureOperatorReaction3_diagonal_rank_two_null_direction]
  exact mul_pos ha hb

theorem curvatureOperatorReaction3_diagonal_rank_two_excluded
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hnull : curvatureOperatorReaction3 (Matrix.diagonal ![a, b, 0]) 2 2 = 0) :
    False := by
  have hpos := curvatureOperatorReaction3_diagonal_rank_two_null_direction_pos ha hb
  linarith

end DifferentialGeometry.Geometry.Curvature.DimensionThree
