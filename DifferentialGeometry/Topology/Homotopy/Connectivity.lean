import DifferentialGeometry.Topology.Homotopy.Adjunction
import DifferentialGeometry.Topology.Homotopy.Reindex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected







noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]



theorem genLoop_pathConnected_of_subsingleton (x : X)
    [Subsingleton (HomotopyGroup N X x)] : PathConnectedSpace (GenLoop N X x) where
  nonempty := ⟨GenLoop.const⟩
  joined p q := by
    have heq := @Subsingleton.elim (HomotopyGroup N X x) inferInstance ⟦p⟧ ⟦q⟧
    exact (genLoop_homotopic_iff_joined p q).mp (Quotient.exact heq)



theorem simplyConnected_of_subsingleton_piOne [PathConnectedSpace X] (x : X)
    [Subsingleton (HomotopyGroup (Fin 1) X x)] : SimplyConnectedSpace X := by
  let : Subsingleton (FundamentalGroup X x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (x := x)).surjective.subsingleton
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun y p => ?_⟩
  let : Subsingleton (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath x y)).surjective.subsingleton
  have heq := @Subsingleton.elim (FundamentalGroup X y) inferInstance
    (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk (Path.refl y))
  exact Path.Homotopic.Quotient.eq.mp heq



theorem genLoop_simplyConnected_of_subsingleton (x : X)
    [Subsingleton (HomotopyGroup N X x)]
    [Subsingleton (HomotopyGroup (Fin 1 ⊕ N) X x)] :
    SimplyConnectedSpace (GenLoop N X x) := by
  let := genLoop_pathConnected_of_subsingleton (N := N) x
  let : Subsingleton (HomotopyGroup (Fin 1) (GenLoop N X x) GenLoop.const) :=
    (homotopyGroupIteratedLoopEquiv (K := Fin 1) (N := N) x).injective.subsingleton
  exact simplyConnected_of_subsingleton_piOne GenLoop.const

end DifferentialGeometry.Topology
