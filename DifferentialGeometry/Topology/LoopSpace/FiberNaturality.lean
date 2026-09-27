import DifferentialGeometry.Topology.LoopSpace.FiberInclusion
import DifferentialGeometry.Topology.LoopSpace.BasedAdjunctionNaturality



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]



theorem basedCircleInclusionHom_natural [DecidableEq N] [Nonempty N]
    (f : C(P, Q)) (p : P)
    (a : HomotopyGroup N (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleInclusionHom (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl (basedCircleInclusionHom p a) := by
  induction a using Quotient.inductionOn with
  | h Γ => rfl



theorem piThreeFreeLoopPiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))]
    (a : HomotopyGroup (Fin 3) P p) :
    piThreeFreeLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl (piThreeFreeLoopPiTwoMulEquiv p a) := by
  have hinv : (basedCirclePiTwoMulEquiv (f p)).symm (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p)
          ((basedCirclePiTwoMulEquiv p).symm a) := by
    apply (basedCirclePiTwoMulEquiv (f p)).injective
    rw [MulEquiv.apply_symm_apply, basedCirclePiTwoMulEquiv_natural, MulEquiv.apply_symm_apply]
  change basedCircleInclusionHom (f p)
      ((basedCirclePiTwoMulEquiv (f p)).symm (homotopyGroupMap f p a)) =
    homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
      (FreeLoop.constants (f p)) rfl
        (basedCircleInclusionHom p ((basedCirclePiTwoMulEquiv p).symm a))
  rw [hinv]
  exact basedCircleInclusionHom_natural f p _

end DifferentialGeometry.Topology
