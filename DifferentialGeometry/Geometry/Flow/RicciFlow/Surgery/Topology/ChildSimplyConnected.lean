import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreSimplyConnected

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem child_simplyConnected_of_childCore_simplyConnected
    (c : ConnectedComponents Q.Carrier) [SimplyConnectedSpace (E.ChildCore c)] :
    SimplyConnectedSpace (Q.component c).Carrier := by
  let r : ℝ := 1 / 2
  have hr : 0 ≤ r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  let : SimplyConnectedSpace (E.childCoreNeighborhood c r) :=
    E.simplyConnectedSpace_childCoreNeighborhood c hr hr1
  let : ∀ b : E.ChildCapBoundary c, SimplyConnectedSpace (E.childCapInterior c b) :=
    fun b => E.simplyConnectedSpace_childCapInterior c b
  let : ∀ b : E.ChildCapBoundary c,
      SimplyConnectedSpace ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b) :=
    fun b => E.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior c b hr1
  exact child_simplyConnected_of_starCover E c (E.childCoreNeighborhood c r)
    (E.childCapInterior c) (E.isOpen_childCoreNeighborhood c r)
    (E.isOpen_childCapInterior c)
    (E.childCoreNeighborhood_union_iUnion_childCapInterior c hr1)
    (E.pairwise_disjoint_childCapInterior c)

theorem child_simplyConnected (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier := by
  let : SimplyConnectedSpace (E.ChildCore c) :=
    E.simplyConnectedSpace_childCore_of_parent_simplyConnected c
  exact E.child_simplyConnected_of_childCore_simplyConnected c

include E in
theorem capped_children_simply_connected
    (hSC : ∀ p : ConnectedComponents P.Carrier,
      SimplyConnectedSpace (P.component p).Carrier) :
    ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (Q.component c).Carrier := by
  intro c
  let := hSC (E.childParent c)
  exact E.child_simplyConnected c

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
