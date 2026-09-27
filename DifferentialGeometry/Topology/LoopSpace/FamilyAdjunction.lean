import DifferentialGeometry.Topology.LoopSpace.FiberNaturality
import DifferentialGeometry.Topology.LoopSpace.HigherConnectivity
import DifferentialGeometry.Topology.LoopSpace.Family
import DifferentialGeometry.Topology.Homotopy.SphereNaturality








noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [SimplyConnectedSpace P] [SimplyConnectedSpace Q]



def freeLoopContractiblePiTwoMulEquiv (q : Q) :
    HomotopyGroup (Fin 2) (freeLoop Q) (FreeLoop.constants q) ≃*
      HomotopyGroup (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants q) :=
  homotopyGroupBasedHomeomorphMulEquiv (contractibleLoopHomeomorphFreeLoop Q).symm
    (FreeLoop.constants q) (ContractibleLoop.constants q) rfl



def piThreeContractibleLoopPiTwoMulEquiv (q : Q)
    [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    HomotopyGroup (Fin 3) Q q ≃*
      HomotopyGroup (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants q) :=
  (piThreeFreeLoopPiTwoMulEquiv q).trans (freeLoopContractiblePiTwoMulEquiv q)



def piThreeLoopFamilyEquiv (q : Q) [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    HomotopyGroup (Fin 3) Q q ≃ loopFamilyClass Q := by
  let := contractibleLoop_simplyConnected_of_piTwo q
  exact (piThreeContractibleLoopPiTwoMulEquiv q).toEquiv.trans
    (homotopyGroupFreeSphereEquiv 1 (ContractibleLoop.constants q))


theorem piThreeLoopFamilyEquiv_one (q : Q) [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    piThreeLoopFamilyEquiv q 1 = LoopFamily.nullClass q := by
  change homotopyGroupToFreeSphere 1 (ContractibleLoop.constants q)
    (piThreeContractibleLoopPiTwoMulEquiv q 1) = _
  rw [map_one]
  exact homotopyGroupToFreeSphere_one 1 (ContractibleLoop.constants q)


theorem piThreeLoopFamilyEquiv_ne_null_iff (q : Q)
    [Subsingleton (HomotopyGroup (Fin 2) Q q)] (a : HomotopyGroup (Fin 3) Q q) :
    piThreeLoopFamilyEquiv q a ≠ LoopFamily.nullClass q ↔ a ≠ 1 := by
  rw [← piThreeLoopFamilyEquiv_one q]
  exact not_congr (piThreeLoopFamilyEquiv q).injective.eq_iff


theorem freeLoopContractiblePiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin 2) (freeLoop P) (FreeLoop.constants p)) :
    freeLoopContractiblePiTwoMulEquiv (f p)
      (homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl a) =
      homotopyGroupBasedMap (ContractibleLoop.postcompose f) (ContractibleLoop.constants p)
        (ContractibleLoop.constants (f p)) rfl (freeLoopContractiblePiTwoMulEquiv p a) := by
  induction a using Quotient.inductionOn with
  | h Γ => rfl


theorem piThreeContractibleLoopPiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))] (a : HomotopyGroup (Fin 3) P p) :
    piThreeContractibleLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (ContractibleLoop.postcompose f) (ContractibleLoop.constants p)
        (ContractibleLoop.constants (f p)) rfl (piThreeContractibleLoopPiTwoMulEquiv p a) := by
  change freeLoopContractiblePiTwoMulEquiv (f p)
      (piThreeFreeLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a)) = _
  rw [piThreeFreeLoopPiTwoMulEquiv_natural, freeLoopContractiblePiTwoMulEquiv_natural]
  rfl



theorem piThreeLoopFamilyEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))] (a : HomotopyGroup (Fin 3) P p) :
    piThreeLoopFamilyEquiv (f p) (homotopyGroupMap f p a) =
      LoopFamily.postcompose f (piThreeLoopFamilyEquiv p a) := by
  change homotopyGroupToFreeSphere 1 (ContractibleLoop.constants (f p))
      (piThreeContractibleLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a)) = _
  rw [piThreeContractibleLoopPiTwoMulEquiv_natural]
  exact homotopyGroupToFreeSphere_natural 1 (ContractibleLoop.postcompose f)
    (ContractibleLoop.constants p) (ContractibleLoop.constants (f p)) rfl
      (piThreeContractibleLoopPiTwoMulEquiv p a)

end DifferentialGeometry.Topology
