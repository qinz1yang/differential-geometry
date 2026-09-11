import Mathlib.Topology.Homotopy.HomotopyGroup



noncomputable section

open Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def genLoopPostcompose (f : C(X, Y)) (x : X) (p : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp p.val, fun y hy => congrArg f (GenLoop.boundary p y hy)⟩


theorem genLoopPostcompose_homotopic (f : C(X, Y)) (x : X)
    {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopPostcompose f x p) (genLoopPostcompose f x q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h f


def homotopyGroupMap (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopPostcompose f x) (fun _ _ h => genLoopPostcompose_homotopic f x h)


theorem homotopyGroupMap_id (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupMap (.id X) x a = a := by
  induction a using Quotient.inductionOn with
  | h p => rfl


theorem homotopyGroupMap_comp {Z : Type*} [TopologicalSpace Z]
    (g : C(Y, Z)) (f : C(X, Y)) (x : X) (a : HomotopyGroup N X x) :
    homotopyGroupMap (g.comp f) x a = homotopyGroupMap g (f x) (homotopyGroupMap f x a) := by
  induction a using Quotient.inductionOn with
  | h p => rfl


theorem genLoopPostcompose_transAt [DecidableEq N] (f : C(X, Y)) (x : X)
    (i : N) (p q : GenLoop N X x) :
    genLoopPostcompose f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopPostcompose f x p) (genLoopPostcompose f x q) := by
  apply GenLoop.ext
  intro t
  simp only [genLoopPostcompose, GenLoop.mk_apply, ContinuousMap.comp_apply,
    GenLoop.transAt, GenLoop.coe_coe, GenLoop.coe_copy]
  split_ifs <;> rfl


def homotopyGroupMapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := homotopyGroupMap f x
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : N := Classical.arbitrary N
        have hmul := congrArg (homotopyGroupMap (N := N) f x)
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        have hconcat := congrArg
          (fun r : GenLoop N Y (f x) => (⟦r⟧ : HomotopyGroup N Y (f x)))
          (genLoopPostcompose_transAt f x i q p)
        exact hconcat.trans (HomotopyGroup.mul_spec (i := i)
          (p := genLoopPostcompose f x p) (q := genLoopPostcompose f x q)).symm


end DifferentialGeometry.Topology
