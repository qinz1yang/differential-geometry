import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.RegularEndpointBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapBoundaryChord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapseRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformSpatialCrossingContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalCanonicalContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalSpatialCanonicalContinuation

set_option autoImplicit false

/-!
# S-CH11-PORT-B1 G4 consumer (`_C11P`)

Type-checks the main theorems of the verbatim-ported astra B1 modules of group G4
(`Surgery/Topology`, `Surgery/ReducedVolume`: canonical continuation, uniform cap windows,
initial-layer ball volume, noncollapsing radius enlargement, Hamilton–Ivey curvature scale).
Own file, no new declarations.
-/

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

example : type_of% @exists_universal_canonicalNeighborhoodContinuation :=
  @exists_universal_canonicalNeighborhoodContinuation

example : type_of% @exists_universal_spatialCanonicalContinuation :=
  @exists_universal_spatialCanonicalContinuation

example : type_of% @exists_uniform_capWindowContinuation := @exists_uniform_capWindowContinuation

example : type_of% @exists_uniform_spatialCrossingContinuation :=
  @exists_uniform_spatialCrossingContinuation

example : type_of% @exists_initial_layer_all_ball_volume_lower_bound :=
  @exists_initial_layer_all_ball_volume_lower_bound

example : type_of% @exists_noncollapsedBefore_radius_enlargement :=
  @exists_noncollapsedBefore_radius_enlargement

example : type_of% @exists_uniform_curvature_bound_on_history_slices :=
  @exists_uniform_curvature_bound_on_history_slices

example : type_of% @exists_test_volume_lower_of_regular_endpoint_block :=
  @exists_test_volume_lower_of_regular_endpoint_block

example : type_of% @GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le :=
  @GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le

example : type_of% @MetricCutCapEvent.PresentedStaticCap.exists_actual_boundary_curve :=
  @MetricCutCapEvent.PresentedStaticCap.exists_actual_boundary_curve
