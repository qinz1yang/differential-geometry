import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Metric.SharpCovectorPerturbation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciSharp_difference_bound_of_small_metric_derivatives
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (v : TangentSpace I x) :
    let b := ricciSharp gRef x v
    let d := ricciSharp g x v - b
    Real.sqrt (gRef.inner x d d) ≤
      (240 * (Module.finrank ℝ E : ℝ) * ε * Real.sqrt (gRef.inner x v v) +
        ε * Real.sqrt (gRef.inner x b b)) / (1 - ε) := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  exact DifferentialGeometry.Geometry.Metric.metricSharp_difference_bound_of_covector_difference
    g gRef x (ricciTensor g x v).toLinearMap (ricciTensor gRef x v).toLinearMap ε
    (240 * (Module.finrank ℝ E : ℝ) * ε * Real.sqrt (gRef.inner x v v))
    (by linarith) (by positivity) (hsmall 0 (by norm_num))
    (abs_ricci_difference_bound_of_small_metric_derivatives g gRef x ε hε hsmall v)

end DifferentialGeometry.Geometry.Curvature
