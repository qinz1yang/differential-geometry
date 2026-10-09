import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphereDiffeomorphismIsotopyConnected
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly
import DifferentialGeometry.Topology.ThreeManifold.CutCapDecompositionAssembly
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem incidenceConnected_of_finiteSurgeryHistory
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (i : Fin H.eventCount) (C : ConnectedComponents (H.stage i.castSucc).Carrier) :
    ((H.cutCapTrace.transition i).cutIncidenceGraph C).Connected :=
  DifferentialGeometry.Topology.FiniteCutCapTrace.cutIncidenceGraph_connected H.cutCapTrace i C

theorem componentConnectedSumDecomposition_iff_localReconstruction
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u}) :
    (∀ i : Fin H.eventCount,
        (H.cutCapTrace.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).localReconstruction :=
  H.cutCapTrace.componentConnectedSumDecomposition_iff_localReconstruction

theorem connectedSum_standardThreeSphere_right_orientedDiffeomorph
    (N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.connectedSum N
        DifferentialGeometry.Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold
      N.toClosedOrientedManifold) :=
  DifferentialGeometry.Topology.connectedSumLaws_holds.1 N

theorem finiteConnectedSum_orientedDiffeomorph_of_forall₂
    (L K : List (DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3))
    (h : List.Forall₂ (fun
        (M N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.finiteConnectedSum L).toClosedOrientedManifold
      (DifferentialGeometry.Topology.finiteConnectedSum K).toClosedOrientedManifold) :=
  DifferentialGeometry.Topology.finiteConnectedSum_congr_of_connectedSumLaws
    DifferentialGeometry.Topology.connectedSumLaws_holds h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
