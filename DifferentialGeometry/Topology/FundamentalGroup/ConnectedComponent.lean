import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.Clopen
import DifferentialGeometry.Topology.Connected.ComponentIn
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem simplyConnectedSpace_connectedComponentIn_iff
    {X : Type*} [TopologicalSpace X] {U : Set X} {x : X} (hx : x ∈ U) :
    SimplyConnectedSpace (connectedComponentIn U x) ↔
      SimplyConnectedSpace (connectedComponent (⟨x, hx⟩ : U)) :=
  (ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff
    (connectedComponentHomeomorphConnectedComponentIn hx).toHomotopyEquiv).symm

theorem surjective_fundamentalGroup_connectedComponent
    {X : Type u} [TopologicalSpace X] (x : X) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(connectedComponent x, X))
      (⟨x, mem_connectedComponent⟩ : connectedComponent x)) := by
  intro p
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
    have hγ (t) : γ t ∈ connectedComponent x :=
      (isConnected_range γ.continuous).subset_connectedComponent γ.source_mem_range
        ⟨t, rfl⟩
    let δ : Path (⟨x, mem_connectedComponent⟩ : connectedComponent x)
        (⟨x, mem_connectedComponent⟩ : connectedComponent x) :=
      { toFun := fun t => ⟨γ t, hγ t⟩
        continuous_toFun := γ.continuous.subtype_mk hγ
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
    change Path.Homotopic.Quotient.mk (δ.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk γ
    congr 1

theorem subsingleton_fundamentalGroup_of_simplyConnected_connectedComponent
    {X : Type u} [TopologicalSpace X] (x : X)
    [SimplyConnectedSpace (connectedComponent x)] :
    Subsingleton (FundamentalGroup X x) :=
  (surjective_fundamentalGroup_connectedComponent x).subsingleton

end DifferentialGeometry.Topology
