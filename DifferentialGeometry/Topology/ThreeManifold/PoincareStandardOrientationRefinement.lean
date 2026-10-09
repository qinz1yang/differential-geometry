import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosedAssociative

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def poincareStandardOrientationRefinement : Prop :=
  ∀ F : ConnectedClosedOrientedManifold.{u} 3,
    isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold

theorem poincareStandardSumClosed_of_orientationRefinement
    (h : poincareStandardOrientationRefinement.{u}) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_associative connectedSumAssociative_holds h

end DifferentialGeometry.Topology
