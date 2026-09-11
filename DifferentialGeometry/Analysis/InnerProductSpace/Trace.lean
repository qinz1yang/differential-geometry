import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Order.Chebyshev

noncomputable section

open scoped BigOperators

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

theorem LinearMap.IsSymmetric.re_trace_sq_le_finrank_mul_re_trace_comp
    {A : V →ₗ[𝕜] V} (hA : A.IsSymmetric) :
    (RCLike.re (LinearMap.trace 𝕜 V A)) ^ 2 ≤ (Module.finrank 𝕜 V : ℝ) * RCLike.re (LinearMap.trace 𝕜 V (A.comp A)) := by
  let b := hA.eigenvectorBasis (show Module.finrank 𝕜 V = Module.finrank 𝕜 V from rfl)
  let d := hA.eigenvalues (show Module.finrank 𝕜 V = Module.finrank 𝕜 V from rfl)
  have hd : LinearMap.toMatrix b.toBasis b.toBasis A = Matrix.diagonal (fun i => (d i : 𝕜)) :=
    hA.toMatrix_eigenvectorBasis rfl
  have hsq : LinearMap.toMatrix b.toBasis b.toBasis (A.comp A) =
      Matrix.diagonal (fun i => (d i : 𝕜) ^ 2) := by
    rw [LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis, hd,
      Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  have htr : LinearMap.trace 𝕜 V A = ∑ i, (d i : 𝕜) := by
    rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis, hd, Matrix.trace_diagonal]
  have htrsq : LinearMap.trace 𝕜 V (A.comp A) = ∑ i, (d i : 𝕜) ^ 2 := by
    rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis, hsq, Matrix.trace_diagonal]
  rw [htr, htrsq]
  simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  simpa only [Finset.card_univ, Fintype.card_fin] using sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := d)


theorem LinearMap.IsSymmetric.trace_sq_le_finrank_mul_trace_comp
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric) :
    (LinearMap.trace ℝ V A) ^ 2 ≤ (Module.finrank ℝ V : ℝ) * LinearMap.trace ℝ V (A.comp A) := by
  exact hA.re_trace_sq_le_finrank_mul_re_trace_comp
