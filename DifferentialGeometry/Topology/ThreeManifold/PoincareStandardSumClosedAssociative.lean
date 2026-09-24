import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosed
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem poincareStandardSumClosed_of_associative
    (hassoc : connectedSumAssociative.{u})
    (hup : ∀ F : ConnectedClosedOrientedManifold.{u} 3,
      isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold) :
    poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_unit_commutative_associative
    sphereUnitLaws_holds connectedSumCommutative_holds hassoc hup

end DifferentialGeometry.Topology
