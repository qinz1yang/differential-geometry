import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem poincareStandardSumClosed_of_unit_commutative_associative
    (hunit : sphereUnitLaws.{u}) (hcomm : connectedSumCommutative.{u})
    (hassoc : connectedSumAssociative.{u})
    (hup : ∀ F : ConnectedClosedOrientedManifold.{u} 3,
      isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold) :
    poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_isOrientedPoincareStandardSumClosed
    (isOrientedPoincareStandardSumClosed_of_connectedSumLaws
      (connectedSumLaws_of_unit_commutative_associative hunit hcomm hassoc)) hup

end DifferentialGeometry.Topology
