import DifferentialGeometry.Analysis.InnerProductSpace.SpectralRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem traceNormalizedCurvatureOperatorMatrixAt_posSemidef_of_mem_nonnegativeCone
    (x : M) (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (traceNormalizedCurvatureOperatorMatrixAt x basis A).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis A, ?_⟩
  intro c
  have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hA 3 c
    (fun i => basis (bivectorIndex3 i).1) (fun i => basis (bivectorIndex3 i).2)
  simpa only [dotProduct, Matrix.mulVec, traceNormalizedCurvatureOperatorMatrixAt_apply,
      Pi.star_apply, star_trivial, algebraicCurvatureOperatorQuadraticEval,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h)

theorem traceNormalizedCurvatureOperatorMatrixAt_eigenvalues_of_image_finrank_eq_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x A) = 1) :
    let d := (traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis A).eigenvalues₀
    0 < d 0 ∧ d 1 = 0 ∧ d 2 = 0 := by
  have hp := traceNormalizedCurvatureOperatorMatrixAt_posSemidef_of_mem_nonnegativeCone
    x basis A hA
  have hr : (traceNormalizedCurvatureOperatorMatrixAt x basis A).rank = 1 := by
    rw [← curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x basis horth]
    exact hrank
  obtain ⟨hpos, hrest⟩ := hp.eigenvalues₀_of_rank_eq_one hr
  exact ⟨hpos, hrest 1 (by decide), hrest 2 (by decide)⟩

theorem traceNormalizedCurvatureOperatorMatrixAt_eigenvalues_pos_of_image_finrank_eq_three
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x A) = 3) (i : Fin 3) :
    0 < (traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis A).eigenvalues₀ i := by
  have hp := traceNormalizedCurvatureOperatorMatrixAt_posSemidef_of_mem_nonnegativeCone
    x basis A hA
  have hr : (traceNormalizedCurvatureOperatorMatrixAt x basis A).rank = 3 := by
    rw [← curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x basis horth]
    exact hrank
  exact hp.eigenvalues₀_pos_of_rank_eq_card hr i

theorem traceNormalizedCurvatureOperatorMatrixAt_eigenvalues_eq_zero_of_image_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (horth : OrthonormalBasisAt g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x A) = 0) (i : Fin 3) :
    (traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis A).eigenvalues₀ i = 0 := by
  have hr : (traceNormalizedCurvatureOperatorMatrixAt x basis A).rank = 0 := by
    rw [← curvatureOperatorImageAt_finrank_eq_traceNormalized_matrix_rank g x basis horth]
    exact hrank
  exact (traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis A).eigenvalues₀_eq_zero_of_rank_eq_zero hr i

theorem leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x A) = 3) :
    0 < leastCurvatureOperatorEigenvalueAt g x A := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  have hpos := traceNormalizedCurvatureOperatorMatrixAt_eigenvalues_pos_of_image_finrank_eq_three
    g x basis horth A hA hrank 2
  have hpos' : 0 < 2 * leastCurvatureOperatorEigenvalueAt g x A :=
    lt_of_lt_of_eq hpos
      (traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue g x basis horth A)
  linarith

theorem leastCurvatureOperatorEigenvalueAt_eq_zero_of_image_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt g x A) = 0) :
    leastCurvatureOperatorEigenvalueAt g x A = 0 := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  have hz := traceNormalizedCurvatureOperatorMatrixAt_eigenvalues_eq_zero_of_image_finrank_eq_zero
    g x basis horth A hrank 2
  have hz' : 2 * leastCurvatureOperatorEigenvalueAt g x A = 0 :=
    (traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue g x basis horth A).symm.trans hz
  linarith

end DifferentialGeometry.Geometry.Curvature.DimensionThree
