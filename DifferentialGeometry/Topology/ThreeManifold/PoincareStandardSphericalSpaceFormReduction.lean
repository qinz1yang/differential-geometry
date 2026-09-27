import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientationReduction
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem factorOrientationClosure_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : factorOrientationClosure.{u} :=
  factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm
    sphereTwoTimesCircleOrientationClosure_holds hform

theorem poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : poincareStandardOrientationRefinement.{u} :=
  poincareStandardOrientationRefinement_of_factorOrientationClosure
    (factorOrientationClosure_of_sphericalSpaceFormOrientationClosure hform)

theorem poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_factorOrientationClosure
    (factorOrientationClosure_of_sphericalSpaceFormOrientationClosure hform)

end DifferentialGeometry.Topology
