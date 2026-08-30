import DifferentialGeometry.Analysis.Calculus.MatrixRiccati
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue,
    Pi.zero_apply] at hv0 hv1
  change dotProduct v (Matrix.mulVec
    (rotatingKernelSkew * B - B * rotatingKernelSkew) v) = 0
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_apply]
  simp only [rotatingKernelSkew, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.sum_univ_two, Fin.isValue, hB01]
  rw [hB01] at hv0
  calc
    _ = 2 * v 1 * (B 0 0 * v 0 + B 1 0 * v 1) -
        2 * v 0 * (B 1 0 * v 0 + B 1 1 * v 1) := by ring
    _ = 0 := by rw [hv0, hv1]; ring

def autonomousRotatingKernelMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![Real.sin t * Real.sin t, -Real.sin t * Real.cos t],
    ![-Real.sin t * Real.cos t, Real.cos t * Real.cos t]]

def autonomousRotatingKernelGenerator (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos t, Real.sin t]

def autonomousRotatingKernelReaction
    (B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotatingKernelSkew * B - B * rotatingKernelSkew

theorem autonomousRotatingKernelMatrix_quadratic (t : ℝ) (v : Fin 2 → ℝ) :
    dotProduct v (Matrix.mulVec (autonomousRotatingKernelMatrix t) v) =
      (Real.sin t * v 0 - Real.cos t * v 1) ^ 2 := by
  simp [autonomousRotatingKernelMatrix, Matrix.mulVec, dotProduct]
  ring

theorem autonomousRotatingKernelMatrix_posSemidef (t : ℝ) :
    (autonomousRotatingKernelMatrix t).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [autonomousRotatingKernelMatrix]
  · intro v
    rw [show star v = v by rfl, autonomousRotatingKernelMatrix_quadratic]
    exact sq_nonneg _

theorem autonomousRotatingKernelMatrix_generator_mem_ker (t : ℝ) :
    Matrix.mulVec (autonomousRotatingKernelMatrix t)
      (autonomousRotatingKernelGenerator t) = 0 := by
  funext i
  fin_cases i <;> simp [autonomousRotatingKernelMatrix,
    autonomousRotatingKernelGenerator, Matrix.mulVec]
  · ring
  · ring

theorem autonomousRotatingKernelGenerator_ne_zero (t : ℝ) :
    autonomousRotatingKernelGenerator t ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 2)
  have h1 := congr_fun h (1 : Fin 2)
  simp only [autonomousRotatingKernelGenerator, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue] at h0 h1
  have htrig := Real.sin_sq_add_cos_sq t
  rw [h0, h1] at htrig
  norm_num at htrig

theorem autonomousRotatingKernelMatrix_kernel_eq_span (t : ℝ) :
    (Matrix.mulVecLin (autonomousRotatingKernelMatrix t)).ker =
      Submodule.span ℝ {autonomousRotatingKernelGenerator t} := by
  apply le_antisymm
  · intro v hv
    have hq : Real.sin t * v 0 - Real.cos t * v 1 = 0 := by
      have hzero : dotProduct v
          (Matrix.mulVec (autonomousRotatingKernelMatrix t) v) = 0 := by
        rw [show Matrix.mulVec (autonomousRotatingKernelMatrix t) v = 0 by
          simpa using hv]
        simp
      rw [autonomousRotatingKernelMatrix_quadratic] at hzero
      exact sq_eq_zero_iff.mp hzero
    have htrig := Real.sin_sq_add_cos_sq t
    have hrel : Real.cos t * v 1 = Real.sin t * v 0 := by
      linarith [hq]
    have hvform : v = (v 0 * Real.cos t + v 1 * Real.sin t) •
        autonomousRotatingKernelGenerator t := by
      funext i
      fin_cases i
      · simp only [Pi.smul_apply, autonomousRotatingKernelGenerator, Fin.isValue]
        calc
          v 0 = v 0 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by rw [htrig]; ring
          _ = v 0 * Real.cos t ^ 2 + (Real.cos t * v 1) * Real.sin t := by
            rw [hrel]
            ring
          _ = (v 0 * Real.cos t + v 1 * Real.sin t) * Real.cos t := by ring
      · simp only [Pi.smul_apply, autonomousRotatingKernelGenerator, Fin.isValue]
        calc
          v 1 = v 1 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by rw [htrig]; ring
          _ = v 1 * Real.sin t ^ 2 + (Real.sin t * v 0) * Real.cos t := by
            rw [← hrel]
            ring
          _ = (v 0 * Real.cos t + v 1 * Real.sin t) * Real.sin t := by ring
    rw [hvform]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro v hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨c, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul,
      autonomousRotatingKernelMatrix_generator_mem_ker, smul_zero]

theorem autonomousRotatingKernelMatrix_kernel_finrank (t : ℝ) :
    Module.finrank ℝ (Matrix.mulVecLin (autonomousRotatingKernelMatrix t)).ker = 1 := by
  rw [autonomousRotatingKernelMatrix_kernel_eq_span, finrank_span_singleton]
  exact autonomousRotatingKernelGenerator_ne_zero t

theorem autonomousRotatingKernelReaction_apply (t : ℝ) :
    autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) =
      ![![2 * Real.sin t * Real.cos t,
          Real.sin t * Real.sin t - Real.cos t * Real.cos t],
        ![Real.sin t * Real.sin t - Real.cos t * Real.cos t,
          -2 * Real.sin t * Real.cos t]] := by
  apply Matrix.ext
  intro i j
  change (rotatingKernelSkew * autonomousRotatingKernelMatrix t) i j -
      (autonomousRotatingKernelMatrix t * rotatingKernelSkew) i j = _
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j
  all_goals simp [autonomousRotatingKernelMatrix, rotatingKernelSkew,
    Fin.sum_univ_two]
  all_goals ring

theorem autonomousRotatingKernelMatrix_hasDerivAt (t : ℝ) :
    HasDerivAt autonomousRotatingKernelMatrix
      (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t)) t := by
  apply DifferentialGeometry.Analysis.hasDerivAt_matrix
    autonomousRotatingKernelMatrix
    (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t)) t
  have h00 : autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 0 0 =
      Real.cos t * Real.sin t + Real.sin t * Real.cos t := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 0)
      (autonomousRotatingKernelReaction_apply t)
    calc
      _ = 2 * Real.sin t * Real.cos t := by simpa using h
      _ = _ := by ring
  have h01 : autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 0 1 =
      -(Real.cos t * Real.cos t + Real.sin t * (-Real.sin t)) := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 1)
      (autonomousRotatingKernelReaction_apply t)
    simpa [sub_eq_add_neg] using h
  have h10 : autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 1 0 =
      -(Real.cos t * Real.cos t + Real.sin t * (-Real.sin t)) := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 1 0)
      (autonomousRotatingKernelReaction_apply t)
    simpa [sub_eq_add_neg] using h
  have h11 : autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 1 1 =
      -Real.sin t * Real.cos t + Real.cos t * (-Real.sin t) := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 1 1)
      (autonomousRotatingKernelReaction_apply t)
    calc
      _ = -(2 * Real.sin t * Real.cos t) := by simpa using h
      _ = _ := by ring
  intro i j
  fin_cases i <;> fin_cases j
  · change HasDerivAt (fun s => autonomousRotatingKernelMatrix s 0 0)
      (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 0 0) t
    rw [h00]
    change HasDerivAt (Real.sin * Real.sin)
      (Real.cos t * Real.sin t + Real.sin t * Real.cos t) t
    exact (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_sin t)
  · change HasDerivAt (fun s => autonomousRotatingKernelMatrix s 0 1)
      (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 0 1) t
    rw [h01]
    have hfun : (fun s => autonomousRotatingKernelMatrix s 0 1) =
        -(Real.sin * Real.cos) := by
      funext s
      simp [autonomousRotatingKernelMatrix, Pi.neg_apply, Pi.mul_apply]
    rw [hfun]
    exact ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).neg
  · change HasDerivAt (fun s => autonomousRotatingKernelMatrix s 1 0)
      (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 1 0) t
    rw [h10]
    have hfun : (fun s => autonomousRotatingKernelMatrix s 1 0) =
        -(Real.sin * Real.cos) := by
      funext s
      simp [autonomousRotatingKernelMatrix, Pi.neg_apply, Pi.mul_apply]
    rw [hfun]
    exact ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).neg
  · change HasDerivAt (fun s => autonomousRotatingKernelMatrix s 1 1)
      (autonomousRotatingKernelReaction (autonomousRotatingKernelMatrix t) 1 1) t
    rw [h11]
    change HasDerivAt (Real.cos * Real.cos)
      (-Real.sin t * Real.cos t + Real.cos t * (-Real.sin t)) t
    exact (Real.hasDerivAt_cos t).mul (Real.hasDerivAt_cos t)

theorem autonomousRotatingKernelMatrix_kernel_changes :
    autonomousRotatingKernelGenerator (Real.pi / 2) ∉
      (Matrix.mulVecLin (autonomousRotatingKernelMatrix 0)).ker := by
  intro h
  have h0 := congr_fun (show Matrix.mulVec (autonomousRotatingKernelMatrix 0)
      (autonomousRotatingKernelGenerator (Real.pi / 2)) = 0 by simpa using h)
    (1 : Fin 2)
  norm_num [autonomousRotatingKernelMatrix,
    autonomousRotatingKernelGenerator, Matrix.mulVec] at h0

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
