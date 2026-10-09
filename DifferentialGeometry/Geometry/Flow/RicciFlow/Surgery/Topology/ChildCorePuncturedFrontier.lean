import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierSeamCollarReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreComponent

set_option autoImplicit false

noncomputable section

open Set Topology

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem puncturedCore_global_hypothesis_refuted :
    (∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
        ¬ SimplyConnectedSpace ↥T.puncturedCore) ∧
      (∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
        Nonempty T.Index ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore) :=
  ⟨exists_tubeSystem_not_simplyConnectedSpace_puncturedCore,
    exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore⟩

theorem componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected
    (M : Type*) [TopologicalSpace M] [TotallyDisconnectedSpace M] :
    (emptyTubeSystem M).componentwiseSimplyConnected := by
  intro c
  have hne : Nonempty (ComponentCarrier c) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
    exact ⟨⟨x, hx⟩⟩
  have hsub : Subsingleton (ComponentCarrier c) :=
    ⟨fun x y => Subtype.ext (by
      have hcomp : x.1 ∈ connectedComponent y.1 :=
        ConnectedComponents.coe_eq_coe'.mp (x.2.trans y.2.symm)
      have hsing : connectedComponent y.1 = {y.1} := connectedComponent_eq_singleton y.1
      rw [hsing] at hcomp
      simpa using hcomp)⟩
  exact SimplyConnectedSpace.ofContractible (ComponentCarrier c)

theorem exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      T.componentwiseSimplyConnected ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore :=
  ⟨Bool, inferInstance, emptyTubeSystem Bool,
    componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected Bool,
    @TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected
      Bool _ (emptyTubeSystem Bool) ⟨fun a => a.elim⟩
      (not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial (X := Bool))⟩

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def ComponentwisePuncturedCoreSimpleConnected : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

theorem nonempty_puncturedCoreComponent_childCoreComponent (c : ConnectedComponents Q.Carrier) :
    (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)).Nonempty := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  exact ⟨⟨(x : E.trace.tubes.core), E.trace.tubes.core_subset_puncturedCore x.2⟩,
    E.trace.tubes.mem_puncturedCoreComponent_of_mem_connectedComponents hx⟩

theorem componentwisePuncturedCore_of_childCoreSimplyConnected
    (h : ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (E.ChildCore c)) :
    E.ComponentwisePuncturedCoreSimpleConnected :=
  fun c => (E.trace.tubes.simplyConnectedSpace_puncturedCoreComponent_iff_coreComponent
    (fun a => E.tube_smooth a) (E.childCoreComponent c)).mpr (h c)

theorem childCoreSimplyConnected_of_componentwisePuncturedCore
    (h : E.ComponentwisePuncturedCoreSimpleConnected) :
    ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (E.ChildCore c) :=
  fun c => E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c (h c)

theorem child_simplyConnected_of_frontiers
    (hcover : E.childCoreCapCoverProducer)
    (hpc : E.ComponentwisePuncturedCoreSimpleConnected)
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_childCarrierCoreCapCover
    (fun c' h' => Classical.choice (hcover c' h')) (fun c' => hpc c') c

theorem child_simplyConnected_of_frontiers_apply
    (hcover : E.childCoreCapCoverProducer)
    (hpc : E.ComponentwisePuncturedCoreSimpleConnected)
    (c : ConnectedComponents Q.Carrier)
    (h : SimplyConnectedSpace (P.component (E.childParent c)).Carrier) :
    SimplyConnectedSpace (Q.component c).Carrier :=
  @SmoothCutCapTransition.child_simplyConnected_of_frontiers P Q D N E hcover hpc c h

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
