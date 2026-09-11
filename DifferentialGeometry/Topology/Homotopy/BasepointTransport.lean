import DifferentialGeometry.Topology.Homotopy.TransportContinuity
import DifferentialGeometry.Topology.Homotopy.TransportComposition
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected








noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X}


def homotopyGroupTransport (n : ℕ) (p : Path x y) :
    HomotopyGroup (Fin (n + 1)) X x → HomotopyGroup (Fin (n + 1)) X y :=
  Quotient.map (genLoopTransport n p) (fun _ _ h => genLoopTransport_homotopic n p h)


theorem homotopyGroupTransport_refl (n : ℕ) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n (Path.refl x) a = a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_refl_homotopic n Γ)


theorem homotopyGroupTransport_trans (n : ℕ) (p : Path x y) (q : Path y z)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n q (homotopyGroupTransport n p a) =
      homotopyGroupTransport n (p.trans q) a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_trans_homotopic n p q Γ)


theorem homotopyGroupTransport_path_homotopic (n : ℕ) {p q : Path x y}
    (h : p.Homotopic q) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p a = homotopyGroupTransport n q a := by
  induction a using Quotient.inductionOn with
  | h Γ => exact Quotient.sound (genLoopTransport_path_homotopic n h Γ)


theorem homotopyGroupTransport_symm (n : ℕ) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p.symm (homotopyGroupTransport n p a) = a := by
  rw [homotopyGroupTransport_trans,
    homotopyGroupTransport_path_homotopic n (Path.Homotopic.trans_symm p), homotopyGroupTransport_refl]



def homotopyGroupBasepointEquiv (n : ℕ) (p : Path x y) :
    HomotopyGroup (Fin (n + 1)) X x ≃ HomotopyGroup (Fin (n + 1)) X y where
  toFun := homotopyGroupTransport n p
  invFun := homotopyGroupTransport n p.symm
  left_inv := homotopyGroupTransport_symm n p
  right_inv a := by
    simpa only [Path.symm_symm] using homotopyGroupTransport_symm n p.symm a


theorem homotopyGroupTransport_natural (n : ℕ) (f : C(X, Y)) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n (p.map f.continuous) (homotopyGroupMap f x a) =
      homotopyGroupMap f y (homotopyGroupTransport n p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg (fun r : GenLoop (Fin (n + 1)) Y (f y) =>
      (⟦r⟧ : HomotopyGroup (Fin (n + 1)) Y (f y))) (genLoopTransport_natural n f p Γ)



theorem homotopyGroupTransport_path_independent [SimplyConnectedSpace X]
    (n : ℕ) (p q : Path x y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupTransport n p a = homotopyGroupTransport n q a :=
  homotopyGroupTransport_path_homotopic n (SimplyConnectedSpace.paths_homotopic p q) a


theorem homotopyGroup_subsingleton_of_path (n : ℕ) (p : Path x y)
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)] :
    Subsingleton (HomotopyGroup (Fin (n + 1)) X y) :=
  (homotopyGroupBasepointEquiv n p).surjective.subsingleton

end DifferentialGeometry.Topology
