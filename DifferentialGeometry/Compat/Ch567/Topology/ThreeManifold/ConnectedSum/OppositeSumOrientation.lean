import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation

/-!
# PORT567 compatibility names: opposite of a connected sum

The later layout states the integration-layout theorem `connectedSumOpposite_holds`
(statement: the `Prop` `connectedSumOpposite`) as the named theorem `connectedSum_opposite`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem connectedSum_opposite (X Y : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).opposite.toClosedOrientedManifold
      (connectedSum X.opposite Y.opposite).toClosedOrientedManifold) :=
  connectedSumOpposite_holds X Y

end DifferentialGeometry.Topology
