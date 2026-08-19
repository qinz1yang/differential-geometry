import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.InnerProductSpace

open scoped Matrix.Norms.Frobenius

variable {m n ι : Type*}

noncomputable def matrixToEuclid
    (A : Matrix m n ℝ) : EuclideanSpace ℝ (m × n) :=
  WithLp.toLp 2 (fun ij : m × n => A ij.1 ij.2)

noncomputable def euclidToMatrix
    (A : EuclideanSpace ℝ (m × n)) : Matrix m n ℝ :=
  Matrix.of (fun i j => A (i, j))

@[simp] theorem matrixToEuclid_euclidToMatrix
    (A : EuclideanSpace ℝ (m × n)) :
    matrixToEuclid (euclidToMatrix A) = A := by
  ext ij
  simp [matrixToEuclid, euclidToMatrix]

@[simp] theorem euclidToMatrix_matrixToEuclid (A : Matrix m n ℝ) :
    euclidToMatrix (matrixToEuclid A) = A := by
  ext i j
  simp [matrixToEuclid, euclidToMatrix]

theorem matrixToEuclid_add (A B : Matrix m n ℝ) :
    matrixToEuclid (A + B) = matrixToEuclid A + matrixToEuclid B := by
  ext ij
  rfl

theorem matrixToEuclid_sub (A B : Matrix m n ℝ) :
    matrixToEuclid (A - B) = matrixToEuclid A - matrixToEuclid B := by
  ext ij
  rfl

theorem matrixToEuclid_smul (c : ℝ) (A : Matrix m n ℝ) :
    matrixToEuclid (c • A) = c • matrixToEuclid A := by
  ext ij
  rfl

@[simp] theorem euclidToMatrix_add
    (A B : EuclideanSpace ℝ (m × n)) :
    euclidToMatrix (A + B) = euclidToMatrix A + euclidToMatrix B := by
  ext i j
  rfl

@[simp] theorem euclidToMatrix_sub
    (A B : EuclideanSpace ℝ (m × n)) :
    euclidToMatrix (A - B) = euclidToMatrix A - euclidToMatrix B := by
  ext i j
  rfl

@[simp] theorem euclidToMatrix_smul
    (c : ℝ) (A : EuclideanSpace ℝ (m × n)) :
    euclidToMatrix (c • A) = c • euclidToMatrix A := by
  ext i j
  rfl

noncomputable def matrixEuclideanLinearEquiv :
    Matrix m n ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (m × n) where
  toFun := matrixToEuclid
  invFun := euclidToMatrix
  left_inv := euclidToMatrix_matrixToEuclid
  right_inv := matrixToEuclid_euclidToMatrix
  map_add' := matrixToEuclid_add
  map_smul' := matrixToEuclid_smul

section Finite

variable [Fintype m] [Fintype n]

theorem matrixToEuclid_norm (A : Matrix m n ℝ) :
    ‖matrixToEuclid A‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold matrixToEuclid
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

@[simp] theorem euclidToMatrix_norm_eq
    (A : EuclideanSpace ℝ (m × n)) :
    ‖euclidToMatrix A‖ = ‖A‖ := by
  rw [← matrixToEuclid_norm (euclidToMatrix A)]
  simp

noncomputable def matrixEuclideanLinearIsometryEquiv :
    Matrix m n ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (m × n) where
  toLinearEquiv := matrixEuclideanLinearEquiv
  norm_map' := matrixToEuclid_norm

theorem inner_matrixToEuclid
    (A : EuclideanSpace ℝ (m × n)) (B : Matrix m n ℝ) :
    inner ℝ A (matrixToEuclid B) =
      ∑ ij : m × n, A ij * B ij.1 ij.2 := by
  simp only [matrixToEuclid, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  have h := RCLike.inner_apply (𝕜 := ℝ) (x := A.ofLp ij) (y := B ij.1 ij.2)
  calc
    inner ℝ (A.ofLp ij) (B ij.1 ij.2) =
        B ij.1 ij.2 * (starRingEnd ℝ) (A.ofLp ij) := h
    _ = A.ofLp ij * B ij.1 ij.2 := by
      simp [starRingEnd]
      ring

theorem euclid_entry_le_norm
    (A : EuclideanSpace ℝ (m × n)) (ij : m × n) :
    |A ij| ≤ ‖A‖ := by
  simpa [abs_of_nonneg] using PiLp.norm_apply_le A ij

end Finite

variable [Fintype ι]

theorem matrixToEuclid_mul_norm_le
    (A B : Matrix ι ι ℝ) :
    ‖matrixToEuclid (A * B)‖ ≤ ‖matrixToEuclid A‖ * ‖matrixToEuclid B‖ := by
  rw [matrixToEuclid_norm, matrixToEuclid_norm, matrixToEuclid_norm]
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

end DifferentialGeometry.Analysis.InnerProductSpace

end
