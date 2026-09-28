import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem subsingleton_fundamentalGroup_associatedFactor (hsum : E.componentConnectedSumDecomposition)
    (C : ConnectedComponents M.Carrier) {p : (M.component C).Carrier}
    (hsc : Subsingleton (FundamentalGroup (M.component C).Carrier p))
    (x : E.tubes.core) (hxC : ConnectedComponents.mk x.1 = C)
    (q : (E.associatedFactor x).Carrier) :
    Subsingleton (FundamentalGroup (E.associatedFactor x).Carrier q) := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, -, -, ⟨ρ⟩⟩ := hsum C L hL
  have hFmem : E.associatedFactor x ∈ L := hL.2.2 _ ⟨x, hxC, rfl⟩
  let y : (finiteConnectedSum (L ++ K)).Carrier := ρ.1 p
  have he := fundamentalGroupMulEquivOfHomotopyEquiv ρ.1.toHomeomorph.toHomotopyEquiv p y rfl
  have hsumSub : Subsingleton (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier y) :=
    @Equiv.subsingleton _ _ he.toEquiv.symm hsc
  exact subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum (L ++ K) _
    (List.mem_append_left _ hFmem) (fun _ => Classical.choice inferInstance) y hsumSub q

theorem subsingleton_fundamentalGroup_discardedComponent
    (hsum : E.componentConnectedSumDecomposition)
    (C : ConnectedComponents M.Carrier) {p : (M.component C).Carrier}
    (hsc : Subsingleton (FundamentalGroup (M.component C).Carrier p))
    (x : E.tubes.core) (d : E.discarded.Carrier) (hxC : ConnectedComponents.mk x.1 = C)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d)
    (q : (E.outgoingFactor (Sum.inr d)).Carrier) :
    Subsingleton (FundamentalGroup (E.outgoingFactor (Sum.inr d)).Carrier q) := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, -, -, ⟨ρ⟩⟩ := hsum C L hL
  have hFmem : E.discarded.component (ConnectedComponents.mk d) ∈ L :=
    hL.2.2 _ ⟨x, hxC, E.associatedFactor_eq_of_presentation_eq_inr x d hd⟩
  let y : (finiteConnectedSum (L ++ K)).Carrier := ρ.1 p
  have he := fundamentalGroupMulEquivOfHomotopyEquiv ρ.1.toHomeomorph.toHomotopyEquiv p y rfl
  have hsumSub : Subsingleton (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier y) :=
    @Equiv.subsingleton _ _ he.toEquiv.symm hsc
  exact subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum (L ++ K) _
    (List.mem_append_left _ hFmem) (fun _ => Classical.choice inferInstance) y hsumSub q

end SphericalCutCapTransition

end DifferentialGeometry.Topology
