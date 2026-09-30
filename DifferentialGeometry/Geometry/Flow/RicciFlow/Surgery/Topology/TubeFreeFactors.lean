import DifferentialGeometry.Topology.VanKampen.FreeFactors.FiniteCollarFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCapGroups
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapFreeFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreSimplyConnected
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.Surgery
universe u

theorem puncturedCore_componentIn_freeFactor {M : Type u} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
    (T : TubeSystem M) (hopen : ∀ a, IsOpen (T.removedBand a))
    {x : M} (hx : x ∈ T.puncturedCore) :
    GC.Group.IsFreeFactor
      (FundamentalGroup ↥(connectedComponentIn T.puncturedCore x)
        ⟨x, mem_connectedComponentIn hx⟩) (FundamentalGroup M x) := by
  let : SimplyConnectedSpace (Sphere 2) := sphereTwoSimplyConnectedSpace
  let c := fun a => T.middleSphereCollar a (hopen a)
  have he : (⋃ a, Set.range (fun y : Sphere 2 =>
      T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))))ᶜ = T.puncturedCore := by
    rw [T.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range hopen]
    simp only [T.middleSphereCollar_zero]
  have h := GC.Topology.isFreeFactor_compl_iUnion c
    (T.pairwise_disjoint_middleSphereCollar_range hopen) (x := x) (by rw [he]; exact hx)
  let E := Homeomorph.setCongr (congrArg (fun A : Set M => connectedComponentIn A x) he)
  let z := (⟨x, mem_connectedComponentIn (show x ∈ _ from he.symm ▸ hx)⟩ :
    ↥(connectedComponentIn (⋃ a, Set.range (fun y : Sphere 2 =>
      T.tube a (y, (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2))))ᶜ x))
  let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
  exact h.congr f (MulEquiv.refl _)

theorem puncturedCore_componentCarrier_freeFactor {M : Type u} [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
    (T : TubeSystem M) (hopen : ∀ a, IsOpen (T.removedBand a)) (x : T.puncturedCore) :
    GC.Group.IsFreeFactor
      (FundamentalGroup (ComponentCarrier (ConnectedComponents.mk x)) ⟨x, rfl⟩)
      (FundamentalGroup M x.val) := by
  have he : ({y : T.puncturedCore | ConnectedComponents.mk y = ConnectedComponents.mk x} :
      Set T.puncturedCore) = connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  let E := (Homeomorph.setCongr he).trans (connectedComponentHomeomorphConnectedComponentIn x.property)
  let z : ComponentCarrier (ConnectedComponents.mk x) := ⟨x, rfl⟩
  let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
  exact (puncturedCore_componentIn_freeFactor T hopen x.property).congr f.symm (MulEquiv.refl _)

theorem child_freeFactor_parent {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (z : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))
    (y : E.ChildCarrier c) :
    GC.Group.IsFreeFactor (FundamentalGroup (E.ChildCarrier c) y)
      (FundamentalGroup (P.component (E.childParent c)).Carrier
        ⟨z.val.val, E.puncturedCoreComponent_mem_parent c z⟩) := by
  let : LocallyPathConnectedSpace P.Carrier :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace P.Carrier
  let : PathConnectedSpace (ComponentCarrier (E.childParent c)) :=
    componentCarrier_pathConnected (E.childParent c)
  let : LocallyPathConnectedSpace (ComponentCarrier (E.childParent c)) :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace (P.component (E.childParent c)).Carrier
  let T := E.trace.tubes.component (E.childParent c)
  let x := E.puncturedCoreComponentIntoParent c z
  have h := puncturedCore_componentCarrier_freeFactor T
    (E.component_removedBand_isOpen (E.childParent c)) x
  let H := E.puncturedCoreComponentHomeomorphParentComponent c z
  let f := fundamentalGroupMulEquivOfHomotopyEquiv H.toHomotopyEquiv z (H z) rfl
  obtain ⟨a⟩ := child_fundamentalGroup_equiv_puncturedCore E c z y
  exact h.congr ((a.trans f).symm) (MulEquiv.refl _)

theorem smooth_retained_freeFactor {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (q : Q.Carrier) :
    ∃ p : P.Carrier, GC.Group.IsFreeFactor (FundamentalGroup Q.Carrier q)
      (FundamentalGroup P.Carrier p) := by
  let c := ConnectedComponents.mk q
  let H := E.trace.tubes.puncturedCoreComponentHomotopyEquivCoreComponent
    E.tube_smooth (E.childCoreComponent c)
  let : PathConnectedSpace (E.ChildCore c) := childCore_pathConnected E c
  let x : E.ChildCore c := Classical.choice inferInstance
  let z := H.invFun x
  let y : E.ChildCarrier c := ⟨q, rfl⟩
  have h := child_freeFactor_parent E c z y
  let a := componentFundamentalGroupEquiv Q.toClosedOrientedManifold c y
  let b := componentFundamentalGroupEquiv P.toClosedOrientedManifold (E.childParent c)
    ⟨z.val.val, E.puncturedCoreComponent_mem_parent c z⟩
  exact ⟨z.val.val, h.congr a b⟩

end GC.Surgery
