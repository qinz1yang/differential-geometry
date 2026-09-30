import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Prime

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff
namespace GC.Topology
universe u

structure SphereSummand (M P : ConnectedClosedOrientedManifold.{u} 3) where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  index : Fin factors.length
  factor_eq : factors.get index = P
  reconstruction : ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum factors).toClosedOrientedManifold M.toClosedOrientedManifold

def SphereSummand.ofPrimeDecomposition {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : PrimeDecomposition M) (i : Fin D.factors.length) : SphereSummand M (D.factors.get i) where
  factors := D.factors
  index := i
  factor_eq := rfl
  reconstruction := D.reconstruction

end GC.Topology
