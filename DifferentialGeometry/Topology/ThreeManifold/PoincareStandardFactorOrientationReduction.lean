import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem poincareStandardOrientationRefinement_of_factorOrientationClosure
    (hstd : factorOrientationClosure.{u}) : poincareStandardOrientationRefinement.{u} :=
  poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
    connectedSumOpposite_holds hstd

theorem poincareStandardSumClosed_of_factorOrientationClosure
    (hstd : factorOrientationClosure.{u}) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_orientationRefinement
    (poincareStandardOrientationRefinement_of_factorOrientationClosure hstd)

end DifferentialGeometry.Topology
