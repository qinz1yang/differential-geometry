import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.PoincareStandard

/-!
# PORT567 compatibility names: projective-space connected sums

Later-layout name of `isPoincareStandard_connectedSum_projectiveThreeSpaceLift`.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardConnectedSum_connectedSum_projectiveThreeSpaceLift :
    isStandardConnectedSum (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier :=
  isPoincareStandard_connectedSum_projectiveThreeSpaceLift

end DifferentialGeometry.Topology
