import DifferentialGeometry.Topology.Homotopy.LoopTopology
import DifferentialGeometry.Topology.Homotopy.Map



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


theorem genLoop_uncurry_apply (x : X) (p : GenLoop K (GenLoop N X x) GenLoop.const)
    (t : K ⊕ N → unitInterval) :
    GenLoop.genLoopGenLoopEquiv x p t = p (t ∘ Sum.inl) (t ∘ Sum.inr) := rfl


theorem genLoop_uncurry_transAt [DecidableEq K] [DecidableEq N]
    (x : X) (i : K) (p q : GenLoop K (GenLoop N X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv x (GenLoop.transAt i p q) =
      GenLoop.transAt (Sum.inl i) (GenLoop.genLoopGenLoopEquiv x p)
        (GenLoop.genLoopGenLoopEquiv x q) := by
  ext t
  simp only [genLoop_uncurry_apply, GenLoop.transAt, GenLoop.coe_copy, Function.comp_apply]
  split_ifs <;> congr 2 <;> funext j <;> simp [Function.update_apply, Function.comp_def]



def homotopyGroupIteratedLoopMulEquiv [DecidableEq K] [DecidableEq N] [Nonempty K] (x : X) :
    HomotopyGroup K (GenLoop N X x) GenLoop.const ≃* HomotopyGroup (K ⊕ N) X x where
  toEquiv := homotopyGroupIteratedLoopEquiv x
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : K := Classical.arbitrary K
        have hmul := congrArg (homotopyGroupIteratedLoopEquiv (K := K) (N := N) x)
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        have heq := congrArg
          (fun r : GenLoop (K ⊕ N) X x => (⟦r⟧ : HomotopyGroup (K ⊕ N) X x))
          (genLoop_uncurry_transAt x i q p)
        exact heq.trans (HomotopyGroup.mul_spec (i := Sum.inl i)
          (p := GenLoop.genLoopGenLoopEquiv x p) (q := GenLoop.genLoopGenLoopEquiv x q)).symm

end DifferentialGeometry.Topology
