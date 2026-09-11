import DifferentialGeometry.Topology.Homotopy.Connectivity
import DifferentialGeometry.Topology.LoopSpace.FreeAdjunction
import DifferentialGeometry.Topology.LoopSpace.SimplyConnectedTarget








noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]


theorem piOne_subsingleton_of_simplyConnected (x : X) :
    Subsingleton (HomotopyGroup (Fin 1) X x) :=
  (HomotopyGroup.pi1EquivFundamentalGroup (x := x)).injective.subsingleton


theorem basedCircle_pathConnected (x : X) : PathConnectedSpace (basedCircleLoop x) := by
  let := piOne_subsingleton_of_simplyConnected x
  let := genLoop_pathConnected_of_subsingleton (N := Fin 1) x
  exact (genLoopCircleHomeomorph x).surjective.pathConnectedSpace
    (genLoopCircleHomeomorph x).continuous


theorem basedCircle_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    SimplyConnectedSpace (basedCircleLoop x) := by
  let := basedCircle_pathConnected x
  let : Subsingleton
      (HomotopyGroup (Fin 1) (basedCircleLoop x) (basedCircleConstant x)) :=
    (basedCirclePiOneMulEquiv x).injective.subsingleton
  exact simplyConnected_of_subsingleton_piOne (basedCircleConstant x)





theorem freeLoop_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] : SimplyConnectedSpace (freeLoop X) := by
  let := piOne_subsingleton_of_simplyConnected x
  let : Subsingleton (HomotopyGroup (Fin 1 ⊕ Fin 1) X x) :=
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) x).injective.subsingleton
  let := genLoop_simplyConnected_of_subsingleton (N := Fin 1) x
  have hs : Subsingleton (HomotopyGroup (Fin 1) (freeLoop X) (FreeLoop.constants x)) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        apply Quotient.sound
        apply (genLoopFreeLoopHomeomorph_homotopic_iff x p q).mp
        exact (FreeLoop.homotopic_iff_joined _ _).mpr (joined_freeLoops _ _)
  exact simplyConnected_of_subsingleton_piOne (FreeLoop.constants x)



theorem contractibleLoop_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    SimplyConnectedSpace (contractibleLoop X) := by
  let := freeLoop_simplyConnected_of_piTwo x
  exact (contractibleLoopHomeomorphFreeLoop X).toHomotopyEquiv.simplyConnectedSpace

end DifferentialGeometry.Topology
