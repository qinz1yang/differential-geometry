import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Mathlib.Data.Real.Pointwise

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators Pointwise
namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem actual_curvature_quadratic_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    {n : ℕ} (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) a v w =
      c * algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) a v w := by
  change (∑ i, ∑ j, a i * a j * metricRm04StandardAt (scaleMetric c hc g) x
      (v i) (w i) (w j) (v j)) =
    c * ∑ i, ∑ j, a i * a j * metricRm04StandardAt g x (v i) (w i) (w j) (v j)
  simp_rw [metricRmStandard_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem actual_identity_quadratic_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    {n : ℕ} (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureIdentityQuadraticEval (scaleMetric c hc g) a v w =
      c ^ 2 * algebraicCurvatureIdentityQuadraticEval g a v w := by
  unfold algebraicCurvatureIdentityQuadraticEval
  simp_rw [scaleMetric_inner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem curvatureOperatorLowerBoundAt_scaleMetric_iff
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) (K : ℝ) :
    curvatureOperatorLowerBoundAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) K ↔
      curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) (c * K) := by
  have hquad (n : ℕ) (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) a v w +
        K * algebraicCurvatureIdentityQuadraticEval (scaleMetric c hc g) a v w =
      c * (algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) a v w +
        (c * K) * algebraicCurvatureIdentityQuadraticEval g a v w) := by
    rw [actual_curvature_quadratic_scale, actual_identity_quadratic_scale]
    ring
  constructor
  · intro h n a v w
    have hh := h n a v w
    rw [hquad] at hh
    exact nonneg_of_mul_nonneg_right hh hc
  · intro h n a v w
    rw [hquad]
    exact mul_nonneg hc.le (h n a v w)

theorem leastCurvatureOperatorEigenvalueAt_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) :
    leastCurvatureOperatorEigenvalueAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) =
      leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) / c := by
  have hsets : {K : ℝ | curvatureOperatorLowerBoundAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) K} =
      c⁻¹ • {K : ℝ | curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K} := by
    ext K
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne')]
    simp only [inv_inv, smul_eq_mul, Set.mem_ofPred_eq]
    exact curvatureOperatorLowerBoundAt_scaleMetric_iff g c hc x K
  unfold leastCurvatureOperatorEigenvalueAt
  rw [hsets, Real.sInf_smul_of_nonneg (inv_nonneg.mpr hc.le)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end DifferentialGeometry.Geometry.Curvature
