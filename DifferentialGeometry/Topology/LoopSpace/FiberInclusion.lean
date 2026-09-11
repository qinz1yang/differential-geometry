import DifferentialGeometry.Topology.LoopSpace.BasedSwap
import DifferentialGeometry.Topology.LoopSpace.FreeHomotopyInjection
import DifferentialGeometry.Topology.LoopSpace.FreeHomotopySurjection
import DifferentialGeometry.Topology.Homotopy.FundamentalLoop
import DifferentialGeometry.Topology.Homotopy.Connectivity








noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] [Nonempty N]


def basedCircleInclusionHom (x : X) :
    HomotopyGroup N (basedCircleLoop x) (basedCircleConstant x) →*
      HomotopyGroup N (freeLoop X) (FreeLoop.constants x) :=
  homotopyGroupBasedMapHom (basedCircleInclusion x) (basedCircleConstant x)
    (FreeLoop.constants x) rfl


theorem basedCircleInclusionHom_injective (x : X) :
    Injective (basedCircleInclusionHom (N := N) x) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      intro h
      apply Quotient.sound
      have hfree := (genLoopFreeLoopHomeomorph_homotopic_iff x _ _).mpr (Quotient.exact h)
      have hj := basedCircle_joined_of_free (genLoopFundamentalGroup_mul_comm (N := N) x)
        (genLoopBasedCircleHomeomorph x p) (genLoopBasedCircleHomeomorph x q) hfree
      apply (genLoop_homotopic_iff_joined p q).mpr
      simpa only [Homeomorph.symm_apply_apply] using
        hj.map (genLoopBasedCircleHomeomorph x).symm.continuous



theorem basedCircleInclusionHom_surjective (x : X)
    [Subsingleton (HomotopyGroup N X x)] :
    Surjective (basedCircleInclusionHom (N := N) x) := by
  let := genLoop_pathConnected_of_subsingleton (N := N) x
  intro b
  induction b using Quotient.inductionOn with
  | h p =>
    obtain ⟨δ, hδ⟩ := exists_basedCircle_free_homotopic
      (GenLoop.const : GenLoop N X x) (genLoopFreeLoopHomeomorph x p)
    let a := (genLoopBasedCircleHomeomorph x).symm δ
    refine ⟨⟦a⟧, Quotient.sound ?_⟩
    apply (genLoopFreeLoopHomeomorph_homotopic_iff x _ p).mp
    change (genLoopBasedCircleHomeomorph x a).val.Homotopic (genLoopFreeLoopHomeomorph x p)
    simpa only [a, Homeomorph.apply_symm_apply] using hδ



def basedCircleInclusionMulEquiv (x : X) [Subsingleton (HomotopyGroup N X x)] :
    HomotopyGroup N (basedCircleLoop x) (basedCircleConstant x) ≃*
      HomotopyGroup N (freeLoop X) (FreeLoop.constants x) :=
  MulEquiv.ofBijective (basedCircleInclusionHom x)
    ⟨basedCircleInclusionHom_injective x, basedCircleInclusionHom_surjective x⟩




def piThreeFreeLoopPiTwoMulEquiv (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    HomotopyGroup (Fin 3) X x ≃*
      HomotopyGroup (Fin 2) (freeLoop X) (FreeLoop.constants x) :=
  (basedCirclePiTwoMulEquiv x).symm.trans (basedCircleInclusionMulEquiv x)

end DifferentialGeometry.Topology
