import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SphereSummand
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Existence

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.GraphManifold
universe u

theorem sphere_split_of_rawGraphPresentation
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) : Nonempty (PrimeDecomposition M) := by
  let _ := G
  exact exists_primeDecomposition M


end GC.GraphManifold
