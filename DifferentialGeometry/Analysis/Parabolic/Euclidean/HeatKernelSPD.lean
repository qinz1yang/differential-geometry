import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLinear
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Positive definite frozen-coordinate reduction

The positive square root of a real positive-definite matrix gives the linear
coordinate equivalence used to conjugate a frozen uniformly elliptic operator
to the isotropic heat operator.  The construction is quantitative: upper and
lower quadratic-form bounds control the operator norms of the equivalence and
its inverse.

No choice of eigenbasis is exposed.  The square root is Mathlib's canonical
continuous-functional-calculus square root, and its square identity supplies
the exact principal-matrix factorization.
-/

noncomputable section

open Matrix Real
open scoped MatrixOrder RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section PositiveDefinite

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The continuous linear equivalence induced by the positive square root of
a positive-definite real matrix. -/
def spdSqrtEquiv (A : Matrix n n ℝ) (hA : A.PosDef) :
    EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n :=
  let hS : (CFC.sqrt A).PosDef := hA.isStrictlyPositive.sqrt.posDef
  (Matrix.toLinearEquiv (EuclideanSpace.basisFun n ℝ).toBasis
      (CFC.sqrt A) (isUnit_iff_ne_zero.mpr hS.det_pos.ne')).toContinuousLinearEquiv

@[simp]
theorem spdSqrtEquiv_apply (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA x = Matrix.toEuclideanCLM (CFC.sqrt A) x := by
  rfl

/-- Applying the square-root equivalence twice applies the original positive
matrix. -/
theorem spdSqrt_comp (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA (spdSqrtEquiv A hA x) =
      Matrix.toEuclideanCLM A x := by
  simp only [spdSqrtEquiv_apply]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

/-- The square-root equivalence is self-adjoint. -/
theorem spdSqrt_selfAdj (A : Matrix n n ℝ) (hA : A.PosDef) :
    IsSelfAdjoint
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) := by
  have heq :
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        Matrix.toEuclideanCLM (CFC.sqrt A) := by
    ext x
    exact spdSqrtEquiv_apply A hA x
  rw [heq]
  exact (CFC.sqrt_nonneg A).isSelfAdjoint.map Matrix.toEuclideanCLM

/-- The norm square after the square-root change of coordinates is the
quadratic form of the original matrix. -/
theorem spdSqrt_norm_sq (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
      ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ := by
  calc
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
        ⟪spdSqrtEquiv A hA x, spdSqrtEquiv A hA x⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪x, spdSqrtEquiv A hA (spdSqrtEquiv A hA x)⟫_ℝ :=
      (spdSqrt_selfAdj A hA).isSymmetric x (spdSqrtEquiv A hA x)
    _ = ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ := by
      rw [spdSqrt_comp]

/-- An upper quadratic-form bound gives the corresponding pointwise bound for
the square-root equivalence. -/
theorem spdSqrt_apply_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ ≤ ellMax * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ≤ √ellMax * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _)),
    spdSqrt_norm_sq, mul_pow, Real.sq_sqrt hMax]
  exact hupper x

/-- Operator-norm form of `spdSqrt_apply_le`. -/
theorem spdSqrt_norm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ ≤ ellMax * ‖x‖ ^ 2) :
    ‖(spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤
      √ellMax := by
  exact ContinuousLinearMap.opNorm_le_bound _ (sqrt_nonneg ellMax)
    (spdSqrt_apply_le A hA hMax hupper)

/-- A positive lower quadratic-form bound controls the inverse square-root
equivalence pointwise. -/
theorem spdSqrt_symm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ)
    (y : EuclideanSpace ℝ n) :
    ‖(spdSqrtEquiv A hA).symm y‖ ≤ (√ellMin)⁻¹ * ‖y‖ := by
  have hsq := hlower ((spdSqrtEquiv A hA).symm y)
  rw [← spdSqrt_norm_sq A hA,
    ContinuousLinearEquiv.apply_symm_apply] at hsq
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hMin)]
  have hsqrt :
      √ellMin * ‖(spdSqrtEquiv A hA).symm y‖ ≤ ‖y‖ := by
    rw [← sq_le_sq₀
      (mul_nonneg (sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _),
      mul_pow, Real.sq_sqrt hMin.le]
    exact hsq
  simpa [mul_comm] using hsqrt

/-- Operator-norm form of the inverse estimate. -/
theorem spdSqrt_inv_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM A x⟫_ℝ) :
    ‖((spdSqrtEquiv A hA).symm :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤ (√ellMin)⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (sqrt_nonneg ellMin))
    (spdSqrt_symm_le A hA hMin hlower)

end PositiveDefinite

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
