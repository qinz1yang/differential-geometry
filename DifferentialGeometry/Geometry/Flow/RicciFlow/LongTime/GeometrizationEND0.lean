import DifferentialGeometry.Geometry.Collapse.GraphThresholdDisjEND0
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctiveApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RouteWLateSequenceC11R
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12Enhanced

/-!
# A universe-zero geometrization certificate

The S-ENDPOINT0 construction uses `exists_graph_threshold_disj_END0` and the parameterised
late-sequence consumer to obtain a geometrization certificate at universe `0`. Its endpoint
has the certificate type of `GC.Endpoint.geometrization_certificate.{0}`. The public theorem
`GC.Endpoint.geometrization` in `LongTime/Geometrization.lean` exposes the prime connected sum,
actual incompressible torus cuts and geometric piece interiors directly.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime

/-- `geometrizes_of_metric` at universe 0 with the static threshold of
`exists_graph_threshold_disj_END0`. -/
theorem geometrizes_of_metric_END0
    (M : ConnectedClosedOrientedManifold.{0} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric) :
    Geometrizes M := by
  obtain ⟨δ, F, _, _, _, _, tests⟩ := Ch11.exists_surgery_with_late_sequence_tests_C11R
    exists_surgery_with_decaying_accuracy_enhanced
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g lateDerivativeOrder
    le_rfl
  exact geometrizes_of_late_slice_supply M F
    (components_geometrize_of_late_sequence_tests_of_static_disj F lateDerivativeOrder
      (exists_graph_threshold_disj_END0 lateDerivativeOrder
        staticDerivativeOrder_le_lateDerivativeOrder) tests)

end GC.LongTime

namespace GC.Endpoint

/-- The universe-zero construction certificate, with the same conclusion as
`geometrization_certificate.{0}`. -/
theorem geometrization_zero_END0 (M : ConnectedClosedOrientedManifold.{0} 3) : Geometrizes M := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.geometrizes_of_metric_END0 M g

theorem geometrization_conjecture_zero_END0 : GeometrizationConjecture.{0} :=
  geometrization_zero_END0

theorem smooth_geometrization_conjecture_zero_END0 : SmoothGeometrizationConjecture.{0} :=
  geometrizationConjecture_iff_smooth.mp geometrization_conjecture_zero_END0

end GC.Endpoint
