import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosure

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_localReconstruction :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  forall_congr' fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).symm


end FiniteCutCapTrace

end DifferentialGeometry.Topology
