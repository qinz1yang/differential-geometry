import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.InnerProductSpace

open scoped Matrix.Norms.Frobenius

variable {m n ι : Type*}

noncomputable def matrixToEuclidean
    (A : Matrix m n ℝ) : EuclideanSpace ℝ (m × n) :=
  WithLp.toLp 2 (fun ij : m × n => A ij.1 ij.2)

noncomputable def euclideanToMatrix
    (A : EuclideanSpace ℝ (m × n)) : Matrix m n ℝ :=
  Matrix.of (fun i j => A (i, j))

@[simp] theorem matrixToEuclidean_apply
    (A : Matrix m n ℝ) (i : m) (j : n) :
    matrixToEuclidean A (i, j) = A i j := by
  simp [matrixToEuclidean]

noncomputable def euclideanMatrixSymmetrization
    (v : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (euclideanToMatrix v + (euclideanToMatrix v).transpose)

theorem euclideanMatrixSymmetrization_isHermitian
    (v : EuclideanSpace ℝ (ι × ι)) : (euclideanMatrixSymmetrization v).IsHermitian := by
  dsimp [euclideanMatrixSymmetrization]
  unfold Matrix.IsHermitian
  ext i j
  simp [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_comm]
  ring

@[simp] theorem matrixToEuclidean_euclideanToMatrix
    (A : EuclideanSpace ℝ (m × n)) :
    matrixToEuclidean (euclideanToMatrix A) = A := by
  ext ij
  simp [matrixToEuclidean, euclideanToMatrix]

@[simp] theorem euclideanToMatrix_matrixToEuclidean (A : Matrix m n ℝ) :
    euclideanToMatrix (matrixToEuclidean A) = A := by
  ext i j
  simp [matrixToEuclidean, euclideanToMatrix]

theorem euclideanMatrixSymmetrization_matrixToEuclidean_symm
    {M : Matrix ι ι ℝ} (hM : M.IsSymm) :
    euclideanMatrixSymmetrization (matrixToEuclidean M) = M := by
  unfold euclideanMatrixSymmetrization
  rw [euclideanToMatrix_matrixToEuclidean]
  ext i j
  have hs : M i j = M j i := by
    have h := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using h.symm
  simp [hs]
  ring

theorem euclideanMatrixSymmetrization_matrixToEuclidean_smul
    (c : ℝ) (M : Matrix ι ι ℝ) :
    euclideanMatrixSymmetrization (matrixToEuclidean (c • M)) = c • euclideanMatrixSymmetrization (matrixToEuclidean M) := by
  unfold euclideanMatrixSymmetrization
  ext i j
  simp only [euclideanToMatrix_matrixToEuclidean, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

theorem euclideanMatrixSymmetrization_matrixToEuclidean_conj
    [Fintype ι] (O M : Matrix ι ι ℝ) :
    euclideanMatrixSymmetrization (matrixToEuclidean (O.transpose * M * O)) =
      O.transpose * euclideanMatrixSymmetrization (matrixToEuclidean M) * O := by
  unfold euclideanMatrixSymmetrization
  simp only [euclideanToMatrix_matrixToEuclidean]
  have hT : (O.transpose * M * O).transpose = O.transpose * M.transpose * O := by
    simp [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  calc
    (1 / 2 : ℝ) • (O.transpose * M * O + (O.transpose * M * O).transpose)
        = (1 / 2 : ℝ) • (O.transpose * M * O + O.transpose * M.transpose * O) := by rw [hT]
    _ = (1 / 2 : ℝ) • (O.transpose * (M * O) + O.transpose * (M.transpose * O)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (1 / 2 : ℝ) • (O.transpose * (M * O + M.transpose * O)) := by
          rw [← Matrix.mul_add]
    _ = (1 / 2 : ℝ) • (O.transpose * ((M + M.transpose) * O)) := by
          rw [Matrix.add_mul]
    _ = (1 / 2 : ℝ) • (O.transpose * (M + M.transpose) * O) := by
          rw [← Matrix.mul_assoc]
    _ = ((1 / 2 : ℝ) • (O.transpose * (M + M.transpose))) * O := by
          rw [← Matrix.smul_mul]
    _ = (O.transpose * ((1 / 2 : ℝ) • (M + M.transpose))) * O := by
          rw [← Matrix.mul_smul]

theorem matrixToEuclidean_add (A B : Matrix m n ℝ) :
    matrixToEuclidean (A + B) = matrixToEuclidean A + matrixToEuclidean B := by
  ext ij
  rfl

theorem matrixToEuclidean_sub (A B : Matrix m n ℝ) :
    matrixToEuclidean (A - B) = matrixToEuclidean A - matrixToEuclidean B := by
  ext ij
  rfl

theorem matrixToEuclidean_smul (c : ℝ) (A : Matrix m n ℝ) :
    matrixToEuclidean (c • A) = c • matrixToEuclidean A := by
  ext ij
  rfl

@[simp] theorem euclideanToMatrix_add
    (A B : EuclideanSpace ℝ (m × n)) :
    euclideanToMatrix (A + B) = euclideanToMatrix A + euclideanToMatrix B := by
  ext i j
  rfl

@[simp] theorem euclideanToMatrix_sub
    (A B : EuclideanSpace ℝ (m × n)) :
    euclideanToMatrix (A - B) = euclideanToMatrix A - euclideanToMatrix B := by
  ext i j
  rfl

@[simp] theorem euclideanToMatrix_smul
    (c : ℝ) (A : EuclideanSpace ℝ (m × n)) :
    euclideanToMatrix (c • A) = c • euclideanToMatrix A := by
  ext i j
  rfl

noncomputable def matrixEuclideanLinearEquiv :
    Matrix m n ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (m × n) where
  toFun := matrixToEuclidean
  invFun := euclideanToMatrix
  left_inv := euclideanToMatrix_matrixToEuclidean
  right_inv := matrixToEuclidean_euclideanToMatrix
  map_add' := matrixToEuclidean_add
  map_smul' := matrixToEuclidean_smul

section Finite

variable [Fintype m] [Fintype n]

theorem matrixToEuclidean_norm (A : Matrix m n ℝ) :
    ‖matrixToEuclidean A‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold matrixToEuclidean
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.sqrt_eq_rpow]
  congr 1
  rw [show (Finset.univ : Finset (m × n)) =
    Finset.univ.product Finset.univ from Finset.univ_product_univ.symm]
  calc
    (∑ ij ∈ Finset.univ.product Finset.univ, ‖A ij.1 ij.2‖ ^ (2 : ℕ)) =
        ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) :=
      Finset.sum_product' Finset.univ Finset.univ
        (fun i j => ‖A i j‖ ^ (2 : ℕ))
    _ = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
      simp

@[simp] theorem euclideanToMatrix_norm_eq
    (A : EuclideanSpace ℝ (m × n)) :
    ‖euclideanToMatrix A‖ = ‖A‖ := by
  rw [← matrixToEuclidean_norm (euclideanToMatrix A)]
  simp

noncomputable def matrixEuclideanLinearIsometryEquiv :
    Matrix m n ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (m × n) where
  toLinearEquiv := matrixEuclideanLinearEquiv
  norm_map' := matrixToEuclidean_norm

theorem inner_matrixToEuclidean
    (A : EuclideanSpace ℝ (m × n)) (B : Matrix m n ℝ) :
    inner ℝ A (matrixToEuclidean B) =
      ∑ ij : m × n, A ij * B ij.1 ij.2 := by
  simp only [matrixToEuclidean, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  have h := RCLike.inner_apply (𝕜 := ℝ) (x := A.ofLp ij) (y := B ij.1 ij.2)
  calc
    inner ℝ (A.ofLp ij) (B ij.1 ij.2) =
        B ij.1 ij.2 * (starRingEnd ℝ) (A.ofLp ij) := h
    _ = A.ofLp ij * B ij.1 ij.2 := by
      change B ij.1 ij.2 * A.ofLp ij = A.ofLp ij * B ij.1 ij.2
      ring

theorem inner_matrixToEuclidean_symm
    [Fintype ι] (v : EuclideanSpace ℝ (ι × ι)) (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) :
    inner ℝ v (matrixToEuclidean A) =
      inner ℝ (matrixToEuclidean (euclideanMatrixSymmetrization v)) (matrixToEuclidean A) := by
  rw [inner_matrixToEuclidean, inner_matrixToEuclidean]
  dsimp [euclideanMatrixSymmetrization]
  have hAij : ∀ i j : ι, A i j = A j i := by
    intro i j
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose] using h.symm
  have hswap :
      (∑ ij : ι × ι, v (ij.2, ij.1) * A ij.1 ij.2) =
        (∑ ij : ι × ι, v (ij.1, ij.2) * A ij.1 ij.2) := by
    calc
      (∑ ij : ι × ι, v (ij.2, ij.1) * A ij.1 ij.2)
          = (∑ ij : ι × ι, v (ij.1, ij.2) * A ij.2 ij.1) := by
            refine Finset.sum_bij (fun ij _ => (ij.2, ij.1)) ?_ ?_ ?_ ?_
            · intro ij _
              simp
            · intro a _ b _ h
              exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
            · intro b _
              refine ⟨(b.2, b.1), ⟨by simp, ?_⟩⟩
              exact Prod.ext rfl rfl
            · intro _ _
              rfl
      _ = (∑ ij : ι × ι, v (ij.1, ij.2) * A ij.1 ij.2) := by
          apply Finset.sum_congr rfl
          intro ij _
          simp [hAij ij.1 ij.2]
  calc
    (∑ ij : ι × ι, v (ij.1, ij.2) * A ij.1 ij.2)
        = (1 / 2 : ℝ) * (∑ ij : ι × ι, v (ij.1, ij.2) * A ij.1 ij.2) +
            (1 / 2 : ℝ) * (∑ ij : ι × ι, v (ij.2, ij.1) * A ij.1 ij.2) := by
          rw [hswap]
          ring
    _ = (∑ ij : ι × ι,
            (1 / 2 : ℝ) * (v (ij.1, ij.2) + v (ij.2, ij.1)) * A ij.1 ij.2) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ij _
          ring

theorem euclid_entry_le_norm
    (A : EuclideanSpace ℝ (m × n)) (ij : m × n) :
    |A ij| ≤ ‖A‖ := by
  simpa [abs_of_nonneg] using PiLp.norm_apply_le A ij

end Finite

variable [Fintype ι]

theorem matrixToEuclidean_mul_norm_le
    (A B : Matrix ι ι ℝ) :
    ‖matrixToEuclidean (A * B)‖ ≤ ‖matrixToEuclidean A‖ * ‖matrixToEuclidean B‖ := by
  rw [matrixToEuclidean_norm, matrixToEuclidean_norm, matrixToEuclidean_norm]
  exact Matrix.frobenius_norm_mul A B

theorem matrixTransposeMul_orthogonal [DecidableEq ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    O.transpose * O = 1 := by
  have hdet : IsUnit O.det := by
    have h : O.det * O.transpose.det = 1 := by
      rw [← Matrix.det_mul, hO, Matrix.det_one]
    have h' : O.det * O.det = 1 := by
      simpa [Matrix.det_transpose] using h
    exact isUnit_iff_exists_inv.mpr ⟨O.det, by rw [h']⟩
  have hinv : O⁻¹ = O.transpose := by
    calc
      O⁻¹ = O⁻¹ * 1 := by rw [mul_one]
      _ = O⁻¹ * (O * O.transpose) := by rw [hO]
      _ = (O⁻¹ * O) * O.transpose := by rw [Matrix.mul_assoc]
      _ = 1 * O.transpose := by rw [Matrix.nonsing_inv_mul O hdet]
      _ = O.transpose := by rw [one_mul]
  calc
    O.transpose * O = O⁻¹ * O := by rw [hinv]
    _ = 1 := Matrix.nonsing_inv_mul O hdet

theorem adjugate_orthogonal_conj [DecidableEq ι]
    (O A : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    (O * A * O.transpose).adjugate = O * A.adjugate * O.transpose := by
  have hOadj : O.adjugate = O.det • O.transpose := by
    have hdet : IsUnit O.det := by
      have h : O.det * O.transpose.det = 1 := by
        rw [← Matrix.det_mul, hO, Matrix.det_one]
      have h' : O.det * O.det = 1 := by
        simpa [Matrix.det_transpose] using h
      exact isUnit_iff_exists_inv.mpr ⟨O.det, by rw [h']⟩
    have hsmul : O⁻¹ * (O.det • 1) = O.det • O⁻¹ := by
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, mul_comm]
    have hadj : O.adjugate = O.det • O⁻¹ := by
      calc
        O.adjugate = 1 * O.adjugate := by rw [one_mul]
        _ = (O⁻¹ * O) * O.adjugate := by rw [Matrix.nonsing_inv_mul O hdet]
        _ = O⁻¹ * (O * O.adjugate) := by rw [Matrix.mul_assoc]
        _ = O⁻¹ * (O.det • 1) := by rw [Matrix.mul_adjugate O]
        _ = O.det • O⁻¹ := hsmul
    have hinv : O⁻¹ = O.transpose := by
      calc
        O⁻¹ = O⁻¹ * 1 := by rw [mul_one]
        _ = O⁻¹ * (O * O.transpose) := by rw [hO]
        _ = (O⁻¹ * O) * O.transpose := by rw [Matrix.mul_assoc]
        _ = 1 * O.transpose := by rw [Matrix.nonsing_inv_mul O hdet]
        _ = O.transpose := by rw [one_mul]
    rw [hinv] at hadj
    exact hadj
  have hOt : O.transpose.adjugate = O.det • O := by
    calc
      O.transpose.adjugate = (O.adjugate).transpose := by
        rw [Matrix.adjugate_transpose]
      _ = (O.det • O.transpose).transpose := by rw [hOadj]
      _ = O.det • O := by simp [Matrix.transpose_smul]
  have hdetSq : O.det * O.det = 1 := by
    have h : (O * O.transpose).det = 1 := by rw [hO, Matrix.det_one]
    simpa [Matrix.det_mul, Matrix.det_transpose] using h
  calc
    (O * A * O.transpose).adjugate = (O * (A * O.transpose)).adjugate := by
      rw [Matrix.mul_assoc]
    _ = (A * O.transpose).adjugate * O.adjugate :=
      Matrix.adjugate_mul_distrib _ _
    _ = (O.transpose.adjugate * A.adjugate) * O.adjugate := by
      rw [Matrix.adjugate_mul_distrib]
    _ = ((O.det • O) * A.adjugate) * (O.det • O.transpose) := by
      rw [hOt, hOadj]
    _ = O * A.adjugate * O.transpose := by
      have hmul : ∀ X : Matrix ι ι ℝ,
          ((O.det • O) * X) * (O.det • O.transpose) =
            (O.det * O.det) • (O * X * O.transpose) := by
        intro X
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
      rw [hmul, hdetSq]
      simp

theorem sum_pair_swap {R : Type*} [AddCommMonoid R]
    (f : ι × ι → R) :
    (∑ p : ι × ι, f (p.2, p.1)) = ∑ p : ι × ι, f p := by
  classical
  refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    simp
  · intro a _ b _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro b _
    refine ⟨(b.2, b.1), ⟨by simp, ?_⟩⟩
    exact Prod.ext rfl rfl
  · intro _ _
    rfl

theorem matrixDot_eq_trace_transpose_mul
    (N A : Matrix ι ι ℝ) :
    (∑ ij : ι × ι, N ij.1 ij.2 * A ij.1 ij.2) =
      Matrix.trace (N.transpose * A) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem inner_matrixToEuclidean_orthogonal_conj [DecidableEq ι]
    (N A O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    inner ℝ (matrixToEuclidean N) (matrixToEuclidean A) =
      inner ℝ (matrixToEuclidean (O.transpose * N * O))
        (matrixToEuclidean (O.transpose * A * O)) := by
  have hOt : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  calc
    inner ℝ (matrixToEuclidean N) (matrixToEuclidean A)
        = (∑ ij : ι × ι, N ij.1 ij.2 * A ij.1 ij.2) := by
          rw [inner_matrixToEuclidean]
          change (∑ ij : ι × ι, N ij.1 ij.2 * A ij.1 ij.2) =
            (∑ ij : ι × ι, N ij.1 ij.2 * A ij.1 ij.2)
          rfl
    _ = Matrix.trace (N.transpose * A) := matrixDot_eq_trace_transpose_mul N A
    _ = Matrix.trace (O.transpose * (N.transpose * A) * O) := by
          have hcyc := Matrix.trace_mul_cycle O.transpose (N.transpose * A) O
          rw [hO] at hcyc
          simpa [Matrix.one_mul] using hcyc.symm
    _ = Matrix.trace ((O.transpose * N * O).transpose * (O.transpose * A * O)) := by
          congr 1
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
          rw [show O * (O.transpose * (A * O)) = A * O by
            rw [← Matrix.mul_assoc, hO]
            simp]
    _ = (∑ ij : ι × ι,
          (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2) :=
          (matrixDot_eq_trace_transpose_mul (O.transpose * N * O)
            (O.transpose * A * O)).symm
    _ = inner ℝ (matrixToEuclidean (O.transpose * N * O))
          (matrixToEuclidean (O.transpose * A * O)) := by
          rw [inner_matrixToEuclidean]
          change (∑ ij : ι × ι,
              (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2) =
            (∑ ij : ι × ι,
              (O.transpose * N * O) ij.1 ij.2 * (O.transpose * A * O) ij.1 ij.2)
          rfl

theorem sum_sq_column_eq_one [DecidableEq ι]
    (O : Matrix ι ι ℝ) (hO : O.transpose * O = 1) (i : ι) :
    (∑ j : ι, (O j i) ^ 2) = 1 := by
  have hdiag : (O.transpose * O) i i = 1 := by
    have h := congrFun (congrFun hO i) i
    simpa [Matrix.one_apply] using h
  have hsum : (O.transpose * O) i i = ∑ j : ι, (O j i) ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [hsum] at hdiag
  exact hdiag

end DifferentialGeometry.Analysis.InnerProductSpace

end
