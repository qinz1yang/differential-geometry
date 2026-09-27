import DifferentialGeometry.Topology.Homotopy.Adjunction



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


def genLoopPostcomposeMap (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x)) :=
  ⟨genLoopPostcompose f x,
    ((continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩


theorem genLoop_uncurry_natural (f : C(X, Y)) (x : X)
    (p : GenLoop K (GenLoop N X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv (f x)
      (genLoopPostcompose (genLoopPostcomposeMap f x) GenLoop.const p) =
        genLoopPostcompose f x (GenLoop.genLoopGenLoopEquiv x p) := by
  ext t
  rfl



theorem homotopyGroupIteratedLoopEquiv_natural (f : C(X, Y)) (x : X)
    (a : HomotopyGroup K (GenLoop N X x) GenLoop.const) :
    homotopyGroupIteratedLoopEquiv (f x)
      (homotopyGroupMap (genLoopPostcomposeMap f x) GenLoop.const a) =
        homotopyGroupMap f x (homotopyGroupIteratedLoopEquiv x a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    exact congrArg
      (fun r : GenLoop (K ⊕ N) Y (f x) => (⟦r⟧ : HomotopyGroup (K ⊕ N) Y (f x)))
      (genLoop_uncurry_natural f x p)

end DifferentialGeometry.Topology
