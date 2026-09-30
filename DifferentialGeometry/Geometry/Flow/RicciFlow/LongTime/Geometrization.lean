import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

theorem geometrization (M : ConnectedClosedOrientedManifold.{u} 3) : Geometrizes M := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.geometrizes_of_metric M g

theorem geometrization_conjecture : GeometrizationConjecture.{u} := geometrization

theorem smooth_geometrization_conjecture : SmoothGeometrizationConjecture.{u} :=
  geometrizationConjecture_iff_smooth.mp geometrization_conjecture

end GC.Endpoint
