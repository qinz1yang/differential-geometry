import DifferentialGeometry.Topology.VanKampen.FreeFactors.StarCoverGroups
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapInterior
import DifferentialGeometry.Topology.VanKampen.ConnectedSumNeckHomotopy
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.Surgery
universe u

theorem componentCarrier_pathConnected {X : Type u} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (c : ConnectedComponents X) :
    PathConnectedSpace (ComponentCarrier c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hs : ({y : X | ConnectedComponents.mk y = ConnectedComponents.mk x} : Set X) =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  change PathConnectedSpace ↥({y : X | ConnectedComponents.mk y = ConnectedComponents.mk x})
  rw [hs, ← pathComponent_eq_connectedComponent x]
  exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponent (x := x))

theorem childCore_pathConnected {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier) :
    PathConnectedSpace (E.ChildCore c) := by
  let := E.coreCharts
  let : LocallyPathConnectedSpace E.trace.tubes.core :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanHalfSpace 3) E.trace.tubes.core
  exact componentCarrier_pathConnected (E.childCoreComponent c)

theorem child_fundamentalGroup_equiv_core {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (x : E.ChildCore c) (y : E.ChildCarrier c) :
    Nonempty (FundamentalGroup (E.ChildCarrier c) y ≃* FundamentalGroup (E.ChildCore c) x) := by
  let r : ℝ := 1 / 2
  have hr : 0 ≤ r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  let H := E.childCoreNeighborhoodHomotopyEquiv c hr hr1
  let : PathConnectedSpace (E.ChildCore c) := childCore_pathConnected E c
  let : PathConnectedSpace (E.childCoreNeighborhood c r) :=
    ThreeManifold.pathConnectedSpace_of_homotopyEquiv H
  let : ∀ b : E.ChildCapBoundary c, SimplyConnectedSpace (E.childCapInterior c b) :=
    fun b => E.simplyConnectedSpace_childCapInterior c b
  let : ∀ b : E.ChildCapBoundary c,
      SimplyConnectedSpace ↥(E.childCoreNeighborhood c r ∩ E.childCapInterior c b) :=
    fun b => E.simplyConnectedSpace_childCoreNeighborhood_inter_childCapInterior c b hr1
  obtain ⟨e⟩ := GC.Topology.star_cover_fundamentalGroup_equiv
    (E.childCoreNeighborhood c r) (E.childCapInterior c)
    (E.isOpen_childCoreNeighborhood c r) (E.isOpen_childCapInterior c)
    (E.childCoreNeighborhood_union_iUnion_childCapInterior c hr1)
    (E.pairwise_disjoint_childCapInterior c) (H x) y
  let a := fundamentalGroupMulEquivOfHomotopyEquiv H x (H x) rfl
  exact ⟨e.trans a.symm⟩

theorem child_fundamentalGroup_equiv_puncturedCore {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (z : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))
    (y : E.ChildCarrier c) :
    Nonempty (FundamentalGroup (E.ChildCarrier c) y ≃*
      FundamentalGroup ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) z) := by
  let H := E.trace.tubes.puncturedCoreComponentHomotopyEquivCoreComponent
    E.tube_smooth (E.childCoreComponent c)
  obtain ⟨e⟩ := child_fundamentalGroup_equiv_core E c (H z) y
  let a := fundamentalGroupMulEquivOfHomotopyEquiv H z (H z) rfl
  exact ⟨e.trans a.symm⟩

theorem child_fundamentalGroup_card_eq_puncturedCore {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (z : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))
    (y : E.ChildCarrier c) :
    Nat.card (FundamentalGroup (E.ChildCarrier c) y) =
      Nat.card (FundamentalGroup
        ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) z) := by
  obtain ⟨e⟩ := child_fundamentalGroup_equiv_puncturedCore E c z y
  exact Nat.card_congr e.toEquiv

end GC.Surgery
