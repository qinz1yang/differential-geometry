import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Reconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure PoincareExtinctionContracts (DiscardedCutOpen : Type u → Prop) where
  geometric : geometricReconstructionBackground.{u}
  terminalStep : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
    Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
  metricStep : isCommonLocalRealization.{u}
  incidenceConnectedInput :
    ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (i : Fin H.eventCount) (C : ConnectedComponents (H.stage i.castSucc).Carrier),
    ((H.cutCapTrace.transition i).cutIncidenceGraph C).Connected
  componentSumInput :
    ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (i : Fin H.eventCount), (H.cutCapTrace.transition i).componentConnectedSumDecomposition
  sumInput : DifferentialGeometry.Topology.poincareStandardSumClosed.{u}
  unitInput : ∀ N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.connectedSum N
        DifferentialGeometry.Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold
      N.toClosedOrientedManifold)
  congruenceInput : ∀ (L K : List (DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)),
    List.Forall₂ (fun (M N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.finiteConnectedSum L).toClosedOrientedManifold
      (DifferentialGeometry.Topology.finiteConnectedSum K).toClosedOrientedManifold)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
