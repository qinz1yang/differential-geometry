import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem connectedSum_sphere_left (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} M).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  connectedSum_sphere_left_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds M

theorem connectedSum_sphere_right (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  connectedSum_sphere_right_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds M

theorem finiteConnectedSum_append (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_connectedSumLaws connectedSumLaws_holds L K

theorem finiteConnectedSum_congr {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws connectedSumLaws_holds hf

theorem finiteConnectedSum_opposite (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum
        (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
  finiteConnectedSum_opposite_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds
    connectedSumOpposite_holds L

end DifferentialGeometry.Topology
