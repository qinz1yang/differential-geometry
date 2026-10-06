import DifferentialGeometry.Geometry.Collapse.GraphThresholdDisjEND0
import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctiveApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWLateSequenceWA2

/-!
# The geometrization endpoint at universe 0 without the two threshold admissions

Lane S-ENDPOINT0, G1 (suffix `_END0`). The public endpoint `GC.Endpoint.geometrization.{u}`
(`LongTime/Geometrization.lean`) reaches the static thresholds through
`GC.LongTime.geometrizes_of_metric` -> `components_geometrize_of_late_sequence_tests` ->
`Collapse.exists_graph_threshold_disj`, whose two direct admissions are the closed and the boundary
threshold (A02, A01 of the X132 ledger). Here the chain is restated at universe `0` with
`exists_graph_threshold_disj_END0` (`GraphThresholdDisjEND0.lean`) as the threshold:

* `components_geometrize_of_late_sequence_tests` is replaced by the tree's already
  parameterised form `components_geometrize_of_late_sequence_tests_of_static_disj`
  (`ThresholdDisjunctiveApplications.lean`, universe-polymorphic, same proof) applied at
  `exists_graph_threshold_disj_END0`;
* `geometrizes_of_metric_END0` and `geometrization_zero_END0` repeat the five lines of
  `geometrizes_of_metric` and the three lines of `geometrization` at universe 0.

This endpoint uses the Route W late-sequence consumer
(`CuspP1.exists_surgery_with_late_sequence_tests_routeW_WA`, re-point of 2026-10-06). The recorded
reachable late-time direct admissions are A09, A12 and A13; the old A08/A10/A11/A14 skeleton
declarations remain present but are not used by this endpoint. The universe-`u` statement is not
claimed for `u > 0`.
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
  obtain ⟨δ, F, _, _, _, _, tests⟩ := CuspP1.exists_surgery_with_late_sequence_tests_routeW_WA
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g lateDerivativeOrder
    le_rfl
  exact geometrizes_of_late_slice_supply M F
    (components_geometrize_of_late_sequence_tests_of_static_disj F lateDerivativeOrder
      (exists_graph_threshold_disj_END0 lateDerivativeOrder
        staticDerivativeOrder_le_lateDerivativeOrder) tests)

end GC.LongTime

namespace GC.Endpoint

/-- **Geometrization at universe 0 without the two threshold admissions** (A01, A02 of the X132
ledger): the statement of `geometrization.{0}`. The late-time admissions A08-A14 remain. -/
theorem geometrization_zero_END0 (M : ConnectedClosedOrientedManifold.{0} 3) : Geometrizes M := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.geometrizes_of_metric_END0 M g

theorem geometrization_conjecture_zero_END0 : GeometrizationConjecture.{0} :=
  geometrization_zero_END0

theorem smooth_geometrization_conjecture_zero_END0 : SmoothGeometrizationConjecture.{0} :=
  geometrizationConjecture_iff_smooth.mp geometrization_conjecture_zero_END0

end GC.Endpoint
