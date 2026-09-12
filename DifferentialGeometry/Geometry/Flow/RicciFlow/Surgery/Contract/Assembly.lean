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
  sumInput : DifferentialGeometry.Topology.poincareStandardSumClosed.{u}
  productInput : ∀ p : DifferentialGeometry.Topology.SphereTwoTimesCircle,
    Nonempty (FundamentalGroup DifferentialGeometry.Topology.SphereTwoTimesCircle p ≃*
      Multiplicative ℤ)
  quotientInput : ∀ (G : DifferentialGeometry.Topology.SphericalSpaceFormGroup)
    (p : G.manifold.Carrier),
    Nonempty (FundamentalGroup G.manifold.Carrier p ≃* G.group)
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
  decompositionInput : ∀ (L : List (DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3))
    (x : (i : Fin L.length) → (L.get i).Carrier)
    (y : (DifferentialGeometry.Topology.finiteConnectedSum L).Carrier),
    Nonempty (FundamentalGroup (DifferentialGeometry.Topology.finiteConnectedSum L).Carrier y ≃*
      Monoid.CoprodI (fun i : Fin L.length =>
        FundamentalGroup (L.get i).Carrier (x i)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
