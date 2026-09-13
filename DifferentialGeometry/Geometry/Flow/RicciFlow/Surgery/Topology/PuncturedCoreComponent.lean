import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreRetraction

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

def componentwiseSimplyConnected : Prop :=
  ∀ c : ConnectedComponents ↥T.puncturedCore, SimplyConnectedSpace (ComponentCarrier c)

theorem componentwiseSimplyConnected_of_simplyConnectedSpace
    [SimplyConnectedSpace ↥T.puncturedCore] : T.componentwiseSimplyConnected := by
  intro c
  have hsub : Subsingleton (ConnectedComponents ↥T.puncturedCore) := inferInstance
  have hset : {x : ↥T.puncturedCore | ConnectedComponents.mk x = c} = univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hsub.elim _ _⟩
  have he : ComponentCarrier c ≃ₜ ↥T.puncturedCore :=
    (Homeomorph.setCongr hset).trans (Homeomorph.Set.univ ↥T.puncturedCore)
  exact he.toHomotopyEquiv.simplyConnectedSpace

theorem componentwiseSimplyConnected_of_isEmpty [IsEmpty T.Index] [SimplyConnectedSpace M] :
    T.componentwiseSimplyConnected :=
  @componentwiseSimplyConnected_of_simplyConnectedSpace M _ T
    ((simplyConnectedSpace_puncturedCore_iff_of_isEmpty T).mpr inferInstance)

end TubeSystem

theorem not_forall_simplyConnectedSpace_puncturedCore :
    ¬ (∀ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      SimplyConnectedSpace ↥T.puncturedCore) := by
  intro h
  obtain ⟨M, htop, T, _, hcon⟩ :=
    exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore
  exact hcon (h M htop T)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
