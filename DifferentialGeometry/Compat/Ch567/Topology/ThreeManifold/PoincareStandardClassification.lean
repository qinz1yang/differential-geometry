import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandard

/-!
# PORT567 compatibility names: standard connected sums of two standard factors

Later-layout name of `isPoincareStandard_connectedSum_of_standardFactor`.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardConnectedSum_connectedSum_of_standardFactor
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (hM : isStandardFactor M) (hN : isStandardFactor N) :
    isStandardConnectedSum (connectedSum M N).Carrier :=
  isPoincareStandard_connectedSum_of_standardFactor M N hM hN

end DifferentialGeometry.Topology
