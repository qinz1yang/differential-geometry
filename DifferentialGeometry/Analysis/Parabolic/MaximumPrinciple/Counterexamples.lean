import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple

def rotatingKernelMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, t], ![t, t ^ 2]]

def rotatingKernelGenerator (t : ℝ) : Fin 2 → ℝ := ![(-1) * t, 1]

def rotatingKernelSkew : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, -1], ![1, 0]]

def rotatingKernelReaction (B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotatingKernelSkew * B - B * rotatingKernelSkew

theorem rotatingKernelMatrix_transpose (t : ℝ) :
    (rotatingKernelMatrix t).transpose = rotatingKernelMatrix t := by
  apply Matrix.ext
  intro i j
  change (rotatingKernelMatrix t) j i = (rotatingKernelMatrix t) i j
  fin_cases i <;> fin_cases j <;> simp [rotatingKernelMatrix]

theorem rotatingKernelMatrix_quadratic (t : ℝ) (v : Fin 2 → ℝ) :
    dotProduct v (Matrix.mulVec (rotatingKernelMatrix t) v) =
      (v 0 + t * v 1) ^ 2 := by
  simp [rotatingKernelMatrix, Matrix.mulVec, dotProduct]
  ring

theorem rotatingKernelMatrix_posSemidef (t : ℝ) :
    (rotatingKernelMatrix t).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rotatingKernelMatrix]
  · intro v
    rw [show star v = v by rfl, rotatingKernelMatrix_quadratic]
    exact sq_nonneg _

theorem rotatingKernelMatrix_generator_mem_ker (t : ℝ) :
    Matrix.mulVec (rotatingKernelMatrix t) (rotatingKernelGenerator t) = 0 := by
  funext i
  fin_cases i <;> simp [rotatingKernelMatrix, rotatingKernelGenerator, Matrix.mulVec]
  ring

theorem rotatingKernelMatrix_generator_ne_zero (t : ℝ) :
    rotatingKernelGenerator t ≠ 0 := by
  intro h
  have h' := congr_fun h (1 : Fin 2)
  simp [rotatingKernelGenerator] at h'

theorem rotatingKernelMatrix_kernel_eq_span (t : ℝ) :
    (Matrix.mulVecLin (rotatingKernelMatrix t)).ker =
      Submodule.span ℝ {rotatingKernelGenerator t} := by
  apply le_antisymm
  · intro v hv
    have hq : v 0 + t * v 1 = 0 := by
      have hzero : dotProduct v (Matrix.mulVec (rotatingKernelMatrix t) v) = 0 := by
        rw [show Matrix.mulVec (rotatingKernelMatrix t) v = 0 by simpa using hv]
        simp
      rw [rotatingKernelMatrix_quadratic] at hzero
      exact sq_eq_zero_iff.mp hzero
    have hvform : v = (v 1) • rotatingKernelGenerator t := by
      funext i
      fin_cases i
      · simp [rotatingKernelGenerator]
        linarith
      · simp [rotatingKernelGenerator]
    rw [hvform]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro v hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨c, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul,
      rotatingKernelMatrix_generator_mem_ker, smul_zero]

theorem rotatingKernelMatrix_kernel_finrank (t : ℝ) :
    Module.finrank ℝ (Matrix.mulVecLin (rotatingKernelMatrix t)).ker = 1 := by
  rw [rotatingKernelMatrix_kernel_eq_span, finrank_span_singleton]
  exact rotatingKernelMatrix_generator_ne_zero t

theorem rotatingKernelMatrix_range_finrank (t : ℝ) :
    Module.finrank ℝ (Matrix.mulVecLin (rotatingKernelMatrix t)).range = 1 := by
  have hdim := (Matrix.mulVecLin (rotatingKernelMatrix t)).finrank_range_add_finrank_ker
  rw [rotatingKernelMatrix_kernel_finrank] at hdim
  norm_num at hdim ⊢
  omega

theorem rotatingKernelMatrix_kernel_at_zero :
    (Matrix.mulVecLin (rotatingKernelMatrix 0)).ker =
      Submodule.span ℝ {rotatingKernelGenerator 0} :=
  rotatingKernelMatrix_kernel_eq_span 0

theorem rotatingKernelMatrix_kernel_at_one_generator_mem :
    rotatingKernelGenerator 1 ∈ (Matrix.mulVecLin (rotatingKernelMatrix 1)).ker := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact rotatingKernelMatrix_generator_mem_ker 1

theorem rotatingKernelMatrix_kernel_changes :
    rotatingKernelGenerator 1 ∉ (Matrix.mulVecLin (rotatingKernelMatrix 0)).ker := by
  intro h
  have h0 := congr_fun (show Matrix.mulVec (rotatingKernelMatrix 0) (rotatingKernelGenerator 1) = 0 by
    simpa [Matrix.mulVecLin_apply] using h) (0 : Fin 2)
  simp [rotatingKernelMatrix, rotatingKernelGenerator, Matrix.mulVec] at h0

theorem rotatingKernelSkew_transpose :
    rotatingKernelSkew.transpose = -rotatingKernelSkew := by
  apply Matrix.ext
  intro i j
  change (rotatingKernelSkew) j i = (-rotatingKernelSkew) i j
  rw [Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [rotatingKernelSkew]

theorem rotatingKernelReaction_transpose_of_symmetric
    {B : Matrix (Fin 2) (Fin 2) ℝ}
    (hB : B.transpose = B) :
    (rotatingKernelReaction B).transpose = rotatingKernelReaction B := by
  unfold rotatingKernelReaction
  have hB01 : B 0 1 = B 1 0 := by
    have h := congr_fun (congr_fun hB 0) 1
    simpa [Matrix.transpose_apply] using h.symm
  apply Matrix.ext
  intro i j
  rw [Matrix.transpose_apply]
  rw [Matrix.sub_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply]
  all_goals simp [rotatingKernelSkew, Fin.sum_univ_two, hB01]
  all_goals ring_nf

theorem rotatingKernelReaction_null_quadratic
    {B : Matrix (Fin 2) (Fin 2) ℝ}
    (hB : B.transpose = B) {v : Fin 2 → ℝ}
    (hv : Matrix.mulVec B v = 0) :
    dotProduct v (Matrix.mulVec (rotatingKernelReaction B) v) = 0 := by
  have hB01 : B 0 1 = B 1 0 := by
    have h := congr_fun (congr_fun hB 0) 1
    simpa [Matrix.transpose_apply] using h.symm
  have hv0 := congr_fun hv 0
  have hv1 := congr_fun hv 1
  simp [Matrix.mulVec] at hv0 hv1
  change dotProduct v (Matrix.mulVec
    (rotatingKernelSkew * B - B * rotatingKernelSkew) v) = 0
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply]
  simp [rotatingKernelSkew, Fin.sum_univ_two, hB01]
  rw [hB01] at hv0
  calc
    _ = 2 * v 1 * (B 0 0 * v 0 + B 1 0 * v 1) -
        2 * v 0 * (B 1 0 * v 0 + B 1 1 * v 1) := by ring
    _ = 0 := by rw [hv0, hv1]; ring

def nonLipschitzReaction (a : ℝ) : ℝ := -2 * Real.sqrt (max a 0)

def rankLossSolution (t : ℝ) : ℝ := (max (1 - t) 0) ^ 2

theorem nonLipschitzReaction_on_square (u : ℝ) (hu : 0 ≤ u) :
    nonLipschitzReaction (u ^ 2) = -2 * u := by
  rw [nonLipschitzReaction, max_eq_left (sq_nonneg u), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hu]

theorem rankLossSolution_nonneg (t : ℝ) : 0 ≤ rankLossSolution t := by
  exact sq_nonneg _

theorem rankLossSolution_pos_of_lt {t : ℝ} (ht : t < 1) :
    0 < rankLossSolution t := by
  rw [rankLossSolution, max_eq_left (le_of_lt (sub_pos.mpr ht))]
  positivity

theorem rankLossSolution_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    rankLossSolution t = 0 := by
  rw [rankLossSolution, max_eq_right (sub_nonpos.mpr ht)]
  simp

theorem rankLossSolution_eq_square_of_lt {t : ℝ} (ht : t < 1) :
    rankLossSolution t = (1 - t) ^ 2 := by
  rw [rankLossSolution, max_eq_left (le_of_lt (sub_pos.mpr ht))]

theorem rankLossSolution_reaction_of_lt {t : ℝ} (ht : t < 1) :
    nonLipschitzReaction (rankLossSolution t) = -2 * (1 - t) := by
  rw [rankLossSolution_eq_square_of_lt ht]
  exact nonLipschitzReaction_on_square (1 - t) (le_of_lt (sub_pos.mpr ht))

end DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple
