import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem binaryConnectedSumLaws_holds : binaryConnectedSumLaws.{u} :=
  binaryConnectedSumLaws_of_unit_assoc_comm_transport sphereUnitLaws_holds
    connectedSumCommutative_holds connectedSumAssociative_holds
    connectedSumOrientedTransport_holds

theorem connectedSumLaws_holds : connectedSumLaws.{u} :=
  connectedSumLaws_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds

end DifferentialGeometry.Topology
