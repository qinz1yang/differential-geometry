import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem curvatureOperatorReactionEndomorphism3_isPositive
    {A : V →ₗ[ℝ] V} (hA : A.IsPositive) :
    (curvatureOperatorReactionEndomorphism3 A).IsPositive := by
  classical
  let n := Module.finrank ℝ V
  let b := hA.isSymmetric.eigenvectorBasis (show Module.finrank ℝ V = n from rfl)
  let d := hA.isSymmetric.eigenvalues (show Module.finrank ℝ V = n from rfl)
  have hd : LinearMap.toMatrix b.toBasis b.toBasis A = Matrix.diagonal d :=
    hA.isSymmetric.toMatrix_eigenvectorBasis rfl
  have hsq : LinearMap.toMatrix b.toBasis b.toBasis (A.comp A) =
      Matrix.diagonal (fun i => d i ^ 2) := by
    rw [LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis, hd,
      Matrix.diagonal_mul_diagonal]
    simp only [pow_two]
  have htr : LinearMap.trace ℝ V A = ∑ i, d i := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, hd, Matrix.trace_diagonal]
  have htrsq : LinearMap.trace ℝ V (A.comp A) = ∑ i, d i ^ 2 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, hsq, Matrix.trace_diagonal]
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact hA.nonneg_eigenvalues rfl i
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis
      (curvatureOperatorReactionEndomorphism3 A) = Matrix.diagonal
      (fun i => 2 * d i ^ 2 - (∑ j, d j) * d i +
        ((∑ j, d j) ^ 2 - ∑ j, d j ^ 2) / 2) := by
    unfold curvatureOperatorReactionEndomorphism3
    simp only [map_add, map_sub, map_smul, LinearMap.toMatrix_id, hsq, hd, htr, htrsq]
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [hmat]
  apply Matrix.PosSemidef.diagonal
  intro i
  have hrest := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ.erase i) (f := d) (fun j _ => hdnonneg j)
  have hsum : ∑ j, d j = d i + ∑ j ∈ Finset.univ.erase i, d j := by
    exact (Finset.add_sum_erase _ d (Finset.mem_univ i)).symm
  have hsumsq : ∑ j, d j ^ 2 = d i ^ 2 + ∑ j ∈ Finset.univ.erase i, d j ^ 2 := by
    exact (Finset.add_sum_erase _ (fun j => d j ^ 2) (Finset.mem_univ i)).symm
  change 0 ≤ 2 * d i ^ 2 - (∑ j, d j) * d i + ((∑ j, d j) ^ 2 - ∑ j, d j ^ 2) / 2
  rw [hsum, hsumsq]
  nlinarith [sq_nonneg (d i)]


theorem curvatureOperatorReactionEndomorphism3_inner_nonneg
    {A : V →ₗ[ℝ] V} (hA : A.IsPositive) (v : V) :
    0 ≤ inner ℝ (curvatureOperatorReactionEndomorphism3 A v) v := by
  exact (curvatureOperatorReactionEndomorphism3_isPositive hA).inner_nonneg_left v

end DifferentialGeometry.Geometry.Curvature.DimensionThree
