import DifferentialGeometry.Geometry.Curvature.HamiltonIveyRegion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBounds
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Analysis.Convex
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem mem_fixedHamiltonIveyRegion_of_leastCurvatureOperator_lower_bound
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    {a : ℝ} (ha : 0 < a) (x : M)
    (hbound : -a⁻¹ ≤ 2 * leastCurvatureOperatorEigenvalueAt g x
      (metricAlgebraicCurvatureTensorAt g x)) :
    (metricScalarAt g x, 2 * leastCurvatureOperatorEigenvalueAt g x
      (metricAlgebraicCurvatureTensorAt g x)) ∈ fixedHamiltonIveyRegion a ∧
      -3 / a ≤ metricScalarAt g x := by
  obtain ⟨basis,horth⟩ := exists_orthonormalBasisAt g x
    (show Module.finrank ℝ (TangentSpace I x) = 3 from hdim)
  let ν := 2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x)
  let B := traceNormalizedMetricCurvatureOperatorMatrixAt g x basis
  have hB : B.IsHermitian := traceNormalizedCurvatureOperatorMatrixAt_isHermitian x basis _
  have hmin : minimumRayleighQuotient3 B = ν := by
    rw [minimumRayleighQuotient3_eq_min_eigenvalue hB]
    exact traceNormalizedCurvatureOperatorMatrixAt_least_eigenvalue g x basis horth _
  have htrace : 3 * ν ≤ metricScalarAt g x := by
    have hh := three_mul_minimumRayleighQuotient3_le_trace hB
    rw [hmin,
      traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt g x basis horth] at hh
    exact hh
  have hν : -a⁻¹ ≤ ν := hbound
  refine ⟨?_,?_⟩
  · change 0 ≤ ν ∨ fixedHamiltonIveyBarrier a (-ν) ≤ metricScalarAt g x
    by_cases hv : 0 ≤ ν
    · exact Or.inl hv
    right
    rw [fixedHamiltonIveyBarrier_eq_hamiltonIveyBarrier]
    exact hamiltonIveyBarrier_initial_le_sectionalSum (by linarith) (inv_pos.mpr ha)
      (by linarith) (by linarith)
  · rw [div_eq_mul_inv]
    linarith

theorem exists_pos_fixedHamiltonIveyRegion_of_compact [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : M,
      (metricScalarAt g x, 2 * leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x)) ∈ fixedHamiltonIveyRegion a ∧
        -3/a ≤ metricScalarAt g x := by
  obtain ⟨K,hK,hbound⟩ := exists_curvatureOperatorLowerBoundAt_metricRm04 g hdim
  refine ⟨(2*K)⁻¹,by positivity,?_⟩
  intro x
  apply mem_fixedHamiltonIveyRegion_of_leastCurvatureOperator_lower_bound g hdim (by positivity) x
  obtain ⟨basis,horth⟩ := exists_orthonormalBasisAt g x
    (show Module.finrank ℝ (TangentSpace I x) = 3 from hdim)
  have hh := (curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
    g x basis horth _ K).mp (hbound x)
  rw [inv_inv]
  change -K ≤ leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) at hh
  linarith

end DifferentialGeometry.Geometry.Curvature.DimensionThree
