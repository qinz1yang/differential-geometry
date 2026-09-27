import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierStarCover
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

noncomputable section

open scoped ContinuousMap

namespace DifferentialGeometry

namespace Topology

universe u v

theorem simplyConnectedSpace_of_homotopyEquiv_of_pathConnected
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) [PathConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace X := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton X x₀).mpr ?_
  exact @Equiv.subsingleton _ _
    (fundamentalGroupMulEquivOfHomotopyEquiv e x₀ (e.toFun x₀) rfl).toEquiv
    (inferInstance : Subsingleton (FundamentalGroup Y (e.toFun x₀)))

end Topology

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def cappedChildHomotopyEquivalentCore (c : ConnectedComponents Q.Carrier) : Prop :=
  Nonempty (E.ChildCore c ≃ₕ Q.Carrier)

theorem childCore_simplyConnected_of_cappedChildHomotopyEquivalentCore
    (c : ConnectedComponents Q.Carrier)
    (hcap : cappedChildHomotopyEquivalentCore E c)
    [PathConnectedSpace (E.ChildCore c)] [SimplyConnectedSpace Q.Carrier] :
    SimplyConnectedSpace (E.ChildCore c) :=
  DifferentialGeometry.Topology.simplyConnectedSpace_of_homotopyEquiv_of_pathConnected
    hcap.some

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
