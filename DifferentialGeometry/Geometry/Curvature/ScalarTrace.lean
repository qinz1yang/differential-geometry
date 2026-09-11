import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

theorem metricScalar_eq_trace_ricciSharp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M] (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt g x = LinearMap.trace ℝ (TangentSpace I x) (ricciSharp g x).toLinearMap := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  rw [metricScalar_eq_scal (I := I) g x]
  rw [scalarCurv_eq_orthonormal_trace (I := I) g x b hb]
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  change (∑ i, ricciTensor g x (b i) (b i)) =
    ∑ i, b.repr (ricciSharp g x (b i)) i
  apply Finset.sum_congr rfl
  intro i _
  have hr : b.repr (ricciSharp g x (b i)) i = g.inner x (ricciSharp g x (b i)) (b i) := by
    rw [basis_repr_eq_sum_inv_inner g x b _ hinv (ricciSharp g x (b i)) i]
    simp [identityInvMetric, diagonalInvMetric]
  exact (inner_ricciSharp g x (b i) (b i)).symm.trans hr.symm

end DifferentialGeometry.Geometry.Curvature
