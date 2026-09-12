import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.Manifold.ClosedOriented

noncomputable section

open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def OrientedThreeStage.toClosedOrientedManifold (P : OrientedThreeStage.{u}) :
    DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 where
  Carrier := P.Carrier
  orientation :=
    { dimension_eq := by simp
      orientation := P.orientation.orientation
      locally_constant := P.orientation.locally_constant }

@[simp] theorem OrientedThreeStage.toClosedOrientedManifold_carrier
    (P : OrientedThreeStage.{u}) :
    P.toClosedOrientedManifold.Carrier = P.Carrier := rfl

@[simp] theorem OrientedThreeStage.toClosedOrientedManifold_orientation_apply
    (P : OrientedThreeStage.{u}) (x : P.Carrier) :
    P.toClosedOrientedManifold.orientation.orientation x = P.orientation.orientation x := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
