import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreRetraction
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem not_simplyConnectedSpace_bool : ¬ SimplyConnectedSpace Bool := by
  intro h
  have hpc : PathConnectedSpace Bool :=
    @SimplyConnectedSpace.instPathConnectedSpace Bool _ h
  exact not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial (X := Bool) hpc

theorem not_simplyConnectedSpace_univ_bool : ¬ SimplyConnectedSpace ↥(univ : Set Bool) :=
  fun h => not_simplyConnectedSpace_bool
    ((Homeomorph.Set.univ Bool).toHomotopyEquiv.simplyConnectedSpace_iff.mp h)

theorem simplyConnectedSpace_singleton_bool (b : Bool) :
    SimplyConnectedSpace ↥({b} : Set Bool) := by
  have : Subsingleton ↥({b} : Set Bool) :=
    ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  have : Nonempty ↥({b} : Set Bool) := ⟨⟨b, rfl⟩⟩
  exact SimplyConnectedSpace.ofContractible ↥({b} : Set Bool)

theorem exists_open_cover_simplyConnected_left_not_simplyConnected_right :
    ∃ (X : Type) (_ : TopologicalSpace X) (U V : Set X) (x₀ : X),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ x₀ ∈ U ∩ V ∧
      SimplyConnectedSpace ↥U ∧ ¬ SimplyConnectedSpace ↥V ∧ ¬ SimplyConnectedSpace X :=
  ⟨Bool, inferInstance, {true}, univ, true,
    isOpen_discrete _, isOpen_univ, by simp, ⟨rfl, mem_univ _⟩,
    simplyConnectedSpace_singleton_bool true, not_simplyConnectedSpace_univ_bool,
    not_simplyConnectedSpace_bool⟩

theorem exists_open_cover_simplyConnected_right_not_simplyConnected_left :
    ∃ (X : Type) (_ : TopologicalSpace X) (U V : Set X) (x₀ : X),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ x₀ ∈ U ∩ V ∧
      ¬ SimplyConnectedSpace ↥U ∧ SimplyConnectedSpace ↥V ∧ ¬ SimplyConnectedSpace X :=
  ⟨Bool, inferInstance, univ, {true}, true,
    isOpen_univ, isOpen_discrete _, by simp, ⟨mem_univ _, rfl⟩,
    not_simplyConnectedSpace_univ_bool, simplyConnectedSpace_singleton_bool true,
    not_simplyConnectedSpace_bool⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
