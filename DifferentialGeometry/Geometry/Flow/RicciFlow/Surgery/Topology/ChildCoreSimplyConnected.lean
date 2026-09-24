import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TubePuncturedCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreTwoCover

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

def tubeComponent (a : T.Index) : ConnectedComponents M :=
  ConnectedComponents.mk (T.tube a (DifferentialGeometry.Topology.sphereTwoNorth, ⟨0, by norm_num⟩))

theorem mk_tube_eq_tubeComponent (a : T.Index) (z : TubeDomain) :
    ConnectedComponents.mk (T.tube a z) = T.tubeComponent a := by
  let : ConnectedSpace (Sphere 2) :=
    inferInstanceAs (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  let : ConnectedSpace (Icc (-2 : ℝ) 2) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
  change ConnectedComponents.mk (T.tube a z) =
    ConnectedComponents.mk (T.tube a (DifferentialGeometry.Topology.sphereTwoNorth, ⟨0, by norm_num⟩))
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact (isPreconnected_range (T.tube a).continuous).subset_connectedComponent
    (Set.mem_range_self (DifferentialGeometry.Topology.sphereTwoNorth, ⟨0, by norm_num⟩)) (Set.mem_range_self z)

def component (p : ConnectedComponents M) : TubeSystem (ComponentCarrier p) where
  Index := {a : T.Index // T.tubeComponent a = p}
  finiteIndex := by
    letI : Finite {a : T.Index // T.tubeComponent a = p} :=
      Finite.of_injective (f := (fun a : {a : T.Index // T.tubeComponent a = p} => a.1))
        Subtype.val_injective
    exact Fintype.ofFinite _
  tube a :=
    ⟨fun z => ⟨T.tube a.1 z, (T.mk_tube_eq_tubeComponent a.1 z).trans a.2⟩,
      (T.tube a.1).continuous.subtype_mk _⟩
  embedding a := by
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact T.embedding a.1
  disjoint := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro x ⟨z, rfl⟩ ⟨w, hw⟩
    exact Set.disjoint_left.mp (T.disjoint (Subtype.val_injective.ne hab))
      (Set.mem_range_self z) ⟨w, congrArg Subtype.val hw⟩

@[simp] theorem component_tube_val (p : ConnectedComponents M) (a : (T.component p).Index)
    (z : TubeDomain) : ((T.component p).tube a z).1 = T.tube a.1 z := rfl

theorem tubeComponent_eq_of_mem_range (p : ConnectedComponents M) {a : T.Index}
    {x : M} (hx : ConnectedComponents.mk x = p) (ha : x ∈ Set.range (T.tube a)) :
    T.tubeComponent a = p := by
  obtain ⟨z, rfl⟩ := ha
  exact (T.mk_tube_eq_tubeComponent a z).symm.trans hx

@[simp] theorem mem_component_middleSphere (p : ConnectedComponents M)
    (a : (T.component p).Index) (x : ComponentCarrier p) :
    x ∈ (T.component p).middleSphere a ↔ x.1 ∈ T.middleSphere a.1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨z, hz, Subtype.ext heq⟩

@[simp] theorem mem_component_removedBand (p : ConnectedComponents M)
    (a : (T.component p).Index) (x : ComponentCarrier p) :
    x ∈ (T.component p).removedBand a ↔ x.1 ∈ T.removedBand a.1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨z, hz, Subtype.ext heq⟩

@[simp] theorem mem_component_positiveTube (p : ConnectedComponents M)
    (a : (T.component p).Index) (x : ComponentCarrier p) :
    x ∈ (T.component p).positiveTube a ↔ x.1 ∈ T.positiveTube a.1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨z, hz, Subtype.ext heq⟩

@[simp] theorem mem_component_negativeTube (p : ConnectedComponents M)
    (a : (T.component p).Index) (x : ComponentCarrier p) :
    x ∈ (T.component p).negativeTube a ↔ x.1 ∈ T.negativeTube a.1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨z, hz, Subtype.ext heq⟩

@[simp] theorem mem_component_puncturedCore (p : ConnectedComponents M)
    (x : ComponentCarrier p) :
    x ∈ (T.component p).puncturedCore ↔ x.1 ∈ T.puncturedCore := by
  rw [(T.component p).mem_puncturedCore_iff, T.mem_puncturedCore_iff]
  constructor
  · intro hx a ha
    let b : (T.component p).Index :=
      ⟨a, T.tubeComponent_eq_of_mem_range p x.2 (T.middleSphere_subset_range a ha)⟩
    exact hx b ((T.mem_component_middleSphere p b x).mpr ha)
  · intro hx a ha
    exact hx a.1 ((T.mem_component_middleSphere p a x).mp ha)

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem component_removedBand_isOpen (p : ConnectedComponents P.Carrier)
    (a : (E.trace.tubes.component p).Index) :
    IsOpen ((E.trace.tubes.component p).removedBand a) := by
  have heq : (E.trace.tubes.component p).removedBand a =
      Subtype.val ⁻¹' E.trace.tubes.removedBand a.1 := by
    ext x
    exact E.trace.tubes.mem_component_removedBand p a x
  rw [heq]
  exact (E.removedBand_isOpen a.1).preimage continuous_subtype_val

theorem component_middleSphereSeparation (p : ConnectedComponents P.Carrier)
    [SimplyConnectedSpace (P.component p).Carrier] :
    (E.trace.tubes.component p).middleSphereSeparation := by
  let : SimplyConnectedSpace (ComponentCarrier p) :=
    inferInstanceAs (SimplyConnectedSpace (P.component p).Carrier)
  let : LocallyPathConnectedSpace (ComponentCarrier p) :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace (P.component p).Carrier
  exact (E.trace.tubes.component p).middleSphereSeparation_of_isOpen_removedBand
    (E.component_removedBand_isOpen p)

theorem parent_middleSphereSeparation (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    (E.trace.tubes.component (E.childParent c)).middleSphereSeparation :=
  E.component_middleSphereSeparation (E.childParent c)

theorem tubeComponent_eq_childParent_of_childCapBoundary (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    E.trace.tubes.tubeComponent b.1.1 = E.childParent c := by
  let y : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth
  have hb := E.childCore_mem_parent c ⟨E.trace.tubes.coreBoundarySphere b.1 y, b.2 y⟩
  exact E.trace.tubes.tubeComponent_eq_of_mem_range (E.childParent c) hb
    ⟨(y, TubeSystem.boundaryLevel b.1.2), rfl⟩

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem component_tubes_componentwiseSimplyConnected
    (p : ConnectedComponents P.Carrier)
    [SimplyConnectedSpace (P.component p).Carrier] :
    (E.trace.tubes.component p).componentwiseSimplyConnected := by
  let _ : SimplyConnectedSpace (ComponentCarrier p) :=
    inferInstanceAs (SimplyConnectedSpace (P.component p).Carrier)
  let _ : LocallyPathConnectedSpace (ComponentCarrier p) :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace (P.component p).Carrier
  exact (E.trace.tubes.component p).componentwiseSimplyConnected_of_isOpen_removedBand
    (E.component_removedBand_isOpen p)

theorem parent_tubes_componentwiseSimplyConnected
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    (E.trace.tubes.component (E.childParent c)).componentwiseSimplyConnected :=
  E.component_tubes_componentwiseSimplyConnected (E.childParent c)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

end

noncomputable section

open Set
open scoped unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem mk_coreFun (s : I) (x : M) :
    ConnectedComponents.mk (T.coreFun (s, x)) = ConnectedComponents.mk x := by
  classical
  by_cases hx : ∃ a, x ∈ T.removedBand a
  · obtain ⟨a, ha⟩ := hx
    rw [T.coreFun_eq_of_mem_removedBand (p := (s, x)) ha]
    exact (T.mk_tube_eq_tubeComponent a _).trans
      (T.tubeComponent_eq_of_mem_range (ConnectedComponents.mk x) rfl
        (T.removedBand_subset_range a ha))
  · rw [T.coreFun_eq_self_of_not_mem (p := (s, x)) (fun a ha => hx ⟨a, ha⟩)]

end TubeSystem

namespace SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem puncturedCoreComponent_mem_parent (c : ConnectedComponents Q.Carrier)
    (x : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :
    ConnectedComponents.mk (x.1.1 : P.Carrier) = E.childParent c := by
  let y : E.ChildCore c :=
    ⟨⟨E.trace.tubes.coreFun ((1 : I), x.1.1),
      E.trace.tubes.coreFun_mem_core (p := ((1 : I), (x.1 : P.Carrier))) x.1.2⟩, x.2⟩
  exact (E.trace.tubes.mk_coreFun 1 x.1.1).symm.trans (E.childCore_mem_parent c y)

def puncturedCoreComponentIntoParent (c : ConnectedComponents Q.Carrier) :
    C(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c),
      (E.trace.tubes.component (E.childParent c)).puncturedCore) :=
  ⟨fun x =>
    ⟨⟨x.1.1, E.puncturedCoreComponent_mem_parent c x⟩,
      (E.trace.tubes.mem_component_puncturedCore (E.childParent c) _).mpr x.1.2⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

@[simp] theorem puncturedCoreComponentIntoParent_val (c : ConnectedComponents Q.Carrier)
    (x : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :
    ((E.puncturedCoreComponentIntoParent c x).1.1 : P.Carrier) = x.1.1 := rfl

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
namespace SmoothCutCapTransition
variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

private def parentPuncturedCoreInclusion (c : ConnectedComponents Q.Carrier) :
    C((E.trace.tubes.component (E.childParent c)).puncturedCore, E.trace.tubes.puncturedCore) :=
  ⟨fun y => ⟨y.1.1,
    (E.trace.tubes.mem_component_puncturedCore (E.childParent c) y.1).mp y.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private theorem puncturedCoreComponent_connected (c : ConnectedComponents Q.Carrier) :
    ConnectedSpace (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) := by
  let : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  obtain ⟨u, hu⟩ := E.trace.tubes.puncturedCoreComponent_eq_connectedComponent
    (fun a => E.tube_smooth a) (E.childCoreComponent c)
  exact isConnected_iff_connectedSpace.mp (hu ▸ isConnected_connectedComponent)

private theorem mem_source_of_mem_target_component (c : ConnectedComponents Q.Carrier)
    (x : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))
    (y : (E.trace.tubes.component (E.childParent c)).puncturedCore)
    (hy : ConnectedComponents.mk y = ConnectedComponents.mk (E.puncturedCoreComponentIntoParent c x)) :
    E.parentPuncturedCoreInclusion c y ∈
      E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c) := by
  let : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  obtain ⟨u, hu⟩ := E.trace.tubes.puncturedCoreComponent_eq_connectedComponent
    (fun a => E.tube_smooth a) (E.childCoreComponent c)
  have hmap := congrArg (E.parentPuncturedCoreInclusion c).continuous.connectedComponentsMap hy
  have hmap' : ConnectedComponents.mk (E.parentPuncturedCoreInclusion c y) =
      ConnectedComponents.mk x.1 := by
    simpa only [Continuous.connectedComponentsMap_mk, parentPuncturedCoreInclusion,
      puncturedCoreComponentIntoParent, ContinuousMap.coe_mk] using hmap
  rw [hu]
  have hx : x.1 ∈ connectedComponent u := hu ▸ x.2
  exact ConnectedComponents.coe_eq_coe'.mp
    (hmap'.trans (ConnectedComponents.coe_eq_coe'.mpr hx))

def puncturedCoreComponentHomeomorphParentComponent (c : ConnectedComponents Q.Carrier)
    (x : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :
    E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c) ≃ₜ
      ComponentCarrier (ConnectedComponents.mk (E.puncturedCoreComponentIntoParent c x)) := by
  let : ConnectedSpace (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :=
    E.puncturedCoreComponent_connected c
  have hmk (z : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :
      ConnectedComponents.mk (E.puncturedCoreComponentIntoParent c z) =
        ConnectedComponents.mk (E.puncturedCoreComponentIntoParent c x) := by
    have hz : ConnectedComponents.mk z = ConnectedComponents.mk x := Subsingleton.elim _ _
    simpa only [Continuous.connectedComponentsMap_mk] using
      congrArg (E.puncturedCoreComponentIntoParent c).continuous.connectedComponentsMap hz
  exact
    { toFun := fun z => ⟨E.puncturedCoreComponentIntoParent c z, hmk z⟩
      invFun := fun y => ⟨E.parentPuncturedCoreInclusion c y.1,
        E.mem_source_of_mem_target_component c x y.1 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (E.puncturedCoreComponentIntoParent c).continuous.subtype_mk _
      continuous_invFun := ((E.parentPuncturedCoreInclusion c).continuous.comp
        continuous_subtype_val).subtype_mk _ }

theorem simplyConnectedSpace_puncturedCoreComponent_of_parent_componentwiseSimplyConnected
    (c : ConnectedComponents Q.Carrier)
    (h : (E.trace.tubes.component (E.childParent c)).componentwiseSimplyConnected) :
    SimplyConnectedSpace (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) := by
  let : ConnectedSpace (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :=
    E.puncturedCoreComponent_connected c
  let x : E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c) := Classical.choice inferInstance
  let := h (ConnectedComponents.mk (E.puncturedCoreComponentIntoParent c x))
  exact (E.puncturedCoreComponentHomeomorphParentComponent c x).toHomotopyEquiv.simplyConnectedSpace

end SmoothCutCapTransition
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem simplyConnectedSpace_puncturedCoreComponent_of_parent_simplyConnected
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) :=
  E.simplyConnectedSpace_puncturedCoreComponent_of_parent_componentwiseSimplyConnected c
    (E.parent_tubes_componentwiseSimplyConnected c)

theorem simplyConnectedSpace_childCore_of_parent_simplyConnected
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (E.ChildCore c) :=
  E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c
    (E.simplyConnectedSpace_puncturedCoreComponent_of_parent_simplyConnected c)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

end
