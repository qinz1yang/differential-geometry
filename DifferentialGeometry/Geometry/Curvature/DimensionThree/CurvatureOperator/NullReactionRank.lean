import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Reaction
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Matrix

theorem ker_le_adjugate_ker_of_null_reaction
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hnull : LinearMap.ker A.mulVecLin ≤
      LinearMap.ker (hamiltonIveyMatrixReaction A).mulVecLin) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker A.adjugate.mulVecLin := by
  intro v hv
  have hQ := hnull hv
  change A *ᵥ v = 0 at hv
  change hamiltonIveyMatrixReaction A *ᵥ v = 0 at hQ
  rw [hamiltonIveyMatrixReaction, Matrix.smul_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_add] at hQ
  change A.adjugate *ᵥ v = 0
  exact (smul_eq_zero.mp hQ).resolve_left (by norm_num)

private theorem diagonal_rank_ne_two_of_null_reaction
    (a b c : ℝ)
    (hnull : ∀ v : Fin 3 → ℝ, Matrix.diagonal ![a, b, c] *ᵥ v = 0 →
      hamiltonIveyMatrixReaction (Matrix.diagonal ![a, b, c]) *ᵥ v = 0) :
    (Matrix.diagonal ![a, b, c]).rank ≠ 2 := by
  classical
  have hzero0 (ha : a = 0) : b * c = 0 := by
    have hv : Matrix.diagonal ![a, b, c] *ᵥ Pi.single (0 : Fin 3) (1 : ℝ) = 0 := by
      simp [ha]
    have hQ := hnull _ hv
    rw [hamiltonIveyMatrixReaction_diagonal, Matrix.diagonal_mulVec_single] at hQ
    simpa [ha] using congrFun hQ 0
  have hzero1 (hb : b = 0) : a * c = 0 := by
    have hv : Matrix.diagonal ![a, b, c] *ᵥ Pi.single (1 : Fin 3) (1 : ℝ) = 0 := by
      simp [hb]
    have hQ := hnull _ hv
    rw [hamiltonIveyMatrixReaction_diagonal, Matrix.diagonal_mulVec_single] at hQ
    simpa [hb] using congrFun hQ 1
  have hzero2 (hc : c = 0) : a * b = 0 := by
    have hv : Matrix.diagonal ![a, b, c] *ᵥ Pi.single (2 : Fin 3) (1 : ℝ) = 0 := by
      simp [hc]
    have hQ := hnull _ hv
    rw [hamiltonIveyMatrixReaction_diagonal, Matrix.diagonal_mulVec_single] at hQ
    simpa [hc] using congrFun hQ 2
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp
  intro hrank
  rw [Matrix.rank_diagonal, Fintype.card_subtype, hfin] at hrank
  simp only [Finset.filter_insert, Finset.filter_singleton] at hrank
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp_all

theorem curvatureOperator_rank_trichotomy_of_null_reaction
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian)
    (hnull : LinearMap.ker A.mulVecLin ≤
      LinearMap.ker (hamiltonIveyMatrixReaction A).mulVecLin) :
    A.rank = 0 ∨ A.rank = 1 ∨ A.rank = 3 := by
  classical
  obtain ⟨O, hO, hdiag⟩ := hermitian_orthogonal_diagonalization hA
  rw [diagonal_eigenvalues_tuple] at hdiag
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![hA.eigenvalues₀ 0, hA.eigenvalues₀ 1, hA.eigenvalues₀ 2]
  have hOinv : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  have hfactor : A = O * B * O.transpose := by
    calc
      A = O * (O.transpose * A * O) * O.transpose := by
        symm
        calc
          O * (O.transpose * A * O) * O.transpose =
              (O * O.transpose) * A * (O * O.transpose) := by
            simp only [Matrix.mul_assoc]
          _ = A := by rw [hO]; simp
      _ = O * B * O.transpose := by rw [hdiag]
  have hcancel (v : Fin 3 → ℝ) : O.transpose *ᵥ (O *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hOinv, Matrix.one_mulVec]
  have hnullB (v : Fin 3 → ℝ) (hv : B *ᵥ v = 0) :
      hamiltonIveyMatrixReaction B *ᵥ v = 0 := by
    have hAv : A *ᵥ (O *ᵥ v) = 0 := by
      rw [hfactor]
      simp only [← Matrix.mulVec_mulVec, hcancel, hv, Matrix.mulVec_zero]
    have hQ : hamiltonIveyMatrixReaction A *ᵥ (O *ᵥ v) = 0 := hnull hAv
    rw [hfactor, hamiltonIveyMatrixReaction_orthogonal_conj O B hO] at hQ
    simp only [← Matrix.mulVec_mulVec, hcancel] at hQ
    have hback := congrArg (fun w : Fin 3 → ℝ => O.transpose *ᵥ w) hQ
    simpa only [hcancel, Matrix.mulVec_zero] using hback
  have hdet : O.det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hO
    simp [Matrix.det_mul, hz] at hd
  have hdetT : O.transpose.det ≠ 0 := by simpa only [Matrix.det_transpose] using hdet
  have hrank : A.rank = B.rank := by
    rw [hfactor, Matrix.rank_mul_eq_left_of_det_ne_zero O.transpose (O * B) hdetT,
      Matrix.rank_mul_eq_right_of_det_ne_zero O B hdet]
  have hne : B.rank ≠ 2 :=
    diagonal_rank_ne_two_of_null_reaction
      (hA.eigenvalues₀ 0) (hA.eigenvalues₀ 1) (hA.eigenvalues₀ 2) hnullB
  have hle : A.rank ≤ 3 := Matrix.rank_le_width A
  omega

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
