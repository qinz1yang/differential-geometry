import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open GC.Topology
namespace GC.Endpoint.NoCuts
universe u

def torusDecomposition (M : ConnectedClosedOrientedManifold.{u} 3) : TorusDecomposition M where
  carrier := carrier M
  components := components M
  boundary := boundary M
  reconstructionAtlas := assembly M
  reconstruction := reconstruction M
  leftPiece := fun i => i.elim0
  rightPiece := fun i => i.elim0
  left_owned := fun i => i.elim0
  right_owned := fun i => i.elim0

end GC.Endpoint.NoCuts
