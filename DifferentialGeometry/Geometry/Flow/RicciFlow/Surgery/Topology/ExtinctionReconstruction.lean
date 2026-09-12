import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction

noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace PoincareControlledExtinction

variable {M : ClosedOrientedManifold.{u} 3}
  {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}

theorem isPoincareStandard [ConnectedSpace M.Carrier] (W : PoincareControlledExtinction M g)
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hsumClosed : poincareStandardSumClosed.{u}) :
    isPoincareStandard M.Carrier :=
  W.history.cutCapTrace.isPoincareStandard_of_initialIdentification
    (fun i => (W.history.cutCapTrace.transition i).localReconstruction_of_incidenceGluing
      (fun C => FiniteCutCapTrace.cutIncidenceGraph_connected _ i C) (hsum i))
    W.controlled (W.history.extinct_trace W.extinct) hsumClosed M W.initial.cutCapIdentification

end PoincareControlledExtinction

end DifferentialGeometry.PDE.RicciFlow.Surgery
