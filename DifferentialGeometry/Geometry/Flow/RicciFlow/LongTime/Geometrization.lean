import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWLateSequenceWA2

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

theorem geometrization (M : ConnectedClosedOrientedManifold.{u} 3) : Geometrizes M := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.CuspP1.geometrizes_of_metric_routeW_WA M g

theorem geometrization_conjecture : GeometrizationConjecture.{u} := geometrization

theorem smooth_geometrization_conjecture : SmoothGeometrizationConjecture.{u} :=
  geometrizationConjecture_iff_smooth.mp geometrization_conjecture

end GC.Endpoint
