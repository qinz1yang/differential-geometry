import DifferentialGeometry.Topology.Homotopy.Adjunction



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N]



def genLoopFundamentalGroupMulEquiv (x : X) :
    FundamentalGroup (GenLoop N X x) GenLoop.const ≃* HomotopyGroup (Fin 1 ⊕ N) X x :=
  (HomotopyGroup.pi1MulEquivFundamentalGroup (X := GenLoop N X x) (x := GenLoop.const)).symm.trans
    (homotopyGroupIteratedLoopMulEquiv x)

omit [DecidableEq N] in
theorem genLoopFundamentalGroup_mul_comm [Nonempty N] (x : X)
    (a b : FundamentalGroup (GenLoop N X x) GenLoop.const) : a * b = b * a := by
  classical
  let : Nontrivial (Fin 1 ⊕ N) :=
    ⟨⟨Sum.inl 0, Sum.inr (Classical.arbitrary N), by intro h; cases h⟩⟩
  apply (genLoopFundamentalGroupMulEquiv x).injective
  simp only [map_mul]
  exact @mul_comm (HomotopyGroup (Fin 1 ⊕ N) X x) _ _ _

end DifferentialGeometry.Topology
