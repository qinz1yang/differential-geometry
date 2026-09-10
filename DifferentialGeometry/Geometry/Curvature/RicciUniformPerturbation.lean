import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciTraceEstimate

noncomputable section
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

namespace Poincare.Geometry.Curvature

theorem abs_ricci_difference_bound_of_small_metric_derivatives
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (v w : TangentSpace I x) :
    |ricciTensor g x v w - ricciTensor gRef x v w| ≤
      240 * (Module.finrank ℝ E : ℝ) * ε *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  have h := abs_ricci_difference_le_of_riemann_difference g gRef gRef x (240 * ε)
    (riemann_difference_bound_of_small_metric_derivatives g gRef x ε hε hsmall) v w
  convert h using 1
  ring

end Poincare.Geometry.Curvature
