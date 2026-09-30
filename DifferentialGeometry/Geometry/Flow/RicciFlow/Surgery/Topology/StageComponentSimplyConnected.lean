import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem OrientedThreeStage.simplyConnectedSpace_connectedComponent (P : OrientedThreeStage.{u})
    (x : P.Carrier) [SimplyConnectedSpace (P.component (ConnectedComponents.mk x)).Carrier] :
    SimplyConnectedSpace (connectedComponent x) := by
  have hs : ((P.componentOpen (ConnectedComponents.mk x) : Set P.Carrier)) =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  let e : (P.component (ConnectedComponents.mk x)).Carrier ≃ₜ connectedComponent x :=
    Homeomorph.setCongr hs
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

theorem RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage
    {P₀ : OrientedThreeStage.{u}} [SimplyConnectedSpace P₀.Carrier] {g₀ : P₀.Metric}
    {B : ℝ} {p₀ : CutoffParameters} {δbound ρbound : ℝ} (H : RetainedCoreHistory.{u})
    (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound) (j : Fin (H.eventCount + 1))
    (x : (H.stage j).Carrier) : SimplyConnectedSpace (connectedComponent x) := by
  let h0 := Extinction.Width.initialIdentification_components_simplyConnected P₀ g₀
    H.toHistory hH.1.some
  have := rfs_simply_connected_history H.toHistory h0 j (ConnectedComponents.mk x)
  exact (H.stage j).simplyConnectedSpace_connectedComponent x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
