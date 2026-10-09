import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# Four-point comparison for an arbitrary metric on a compact manifold

The induced-metric package and the completeness adapter supply the metric-space inputs
of the eight-ball comparison theorem from the given smooth metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]

theorem fourPointComparison_of_sectional_lower_bound_on_compact_induced_ball
    (g : SmoothRiemannianMetric I M) (o : M) {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ riemannianBallOf g o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    letI := inducedMetricSpace g
    fourPointComparison κ (riemannianBallOf g o R) := by
  have hg : RiemannianMetricComplete (I := I) g :=
    riemannianMetricComplete_iff_inducedEMetricSpace.mpr
      (inducedEMetricSpace_completeSpace g)
  let := inducedMetricSpace g
  let : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  rw [← inducedMetricSpace_ball g o R]
  apply fourPointComparison_of_sectional_lower_bound_on_eight_ball
    g (inducedMetricSpace_hmetric g) o hκ
  intro y hy
  rw [inducedMetricSpace_ball g o (8 * R)] at hy
  exact hsec y hy

end DifferentialGeometry.Geometry.Comparison.Toponogov
