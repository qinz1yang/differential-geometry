import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Geometry.Metric

theorem sqrt_inner_comparison_of_metric_difference
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (δ : ℝ) (hδ : δ < 1)
    (hmetric : metricDerivNorm 0 g gRef gRef x ≤ δ) (v : TangentSpace I x) :
    Real.sqrt (1 - δ) * Real.sqrt (gRef.inner x v v) ≤ Real.sqrt (g.inner x v v) ∧
      Real.sqrt (g.inner x v v) ≤ Real.sqrt (1 + δ) * Real.sqrt (gRef.inner x v v) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hmetric
  have hv0 := metric_inner_self_nonneg gRef x v
  have h := metricDifference_abs_le g gRef gRef x v v
  rw [mul_assoc, Real.mul_self_sqrt hv0] at h
  have hb := abs_le.mp (h.trans (mul_le_mul_of_nonneg_right hmetric hv0))
  constructor
  · rw [← Real.sqrt_mul (show 0 ≤ 1 - δ by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith [hb.1])
  · rw [← Real.sqrt_mul (show 0 ≤ 1 + δ by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith [hb.2])

end DifferentialGeometry.Geometry.Metric
