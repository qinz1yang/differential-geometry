import DifferentialGeometry.Topology.LoopSpace.CircleCurryFamilies
import DifferentialGeometry.Topology.LoopSpace.FamilyAdjunction



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q] {x y : Q}



theorem circleCurryFreeGenLoop_transport_homotopic (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 2)) Q x) :
    GenLoop.Homotopic (circleCurryFreeGenLoop n y (genLoopTransport (n + 1) p Γ))
      (genLoopTransport n (p.map FreeLoop.constants.continuous) (circleCurryFreeGenLoop n x Γ)) :=
  genLoopTransport_extension_unique n (p.map FreeLoop.constants.continuous)
    (circleCurryFreeGenLoop n x Γ) _ (circleCurryExtension n p Γ)
    (circleCurryExtension_zero n p Γ) (circleCurryExtension_one n p Γ)
    (circleCurryExtension_boundary n p Γ)


theorem piThreeFreeLoopPiTwoMulEquiv_mk (q : Q)
    [Subsingleton (HomotopyGroup (Fin 2) Q q)] (Γ : GenLoop (Fin 3) Q q) :
    piThreeFreeLoopPiTwoMulEquiv q ⟦Γ⟧ = ⟦circleCurryFreeGenLoop 1 q Γ⟧ := by
  exact congrArg (basedCircleInclusionHom q) (basedCirclePiTwoMulEquiv_symm_mk q Γ)



theorem piThreeFreeLoopPiTwoMulEquiv_transport (p : Path x y)
    [Subsingleton (HomotopyGroup (Fin 2) Q x)]
    [Subsingleton (HomotopyGroup (Fin 2) Q y)] (a : HomotopyGroup (Fin 3) Q x) :
    piThreeFreeLoopPiTwoMulEquiv y (homotopyGroupTransport 2 p a) =
      homotopyGroupTransport 1 (p.map FreeLoop.constants.continuous)
        (piThreeFreeLoopPiTwoMulEquiv x a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    have hc : (⟦circleCurryFreeGenLoop 1 y (genLoopTransport 2 p Γ)⟧ :
        HomotopyGroup (Fin 2) (freeLoop Q) (FreeLoop.constants y)) =
        ⟦genLoopTransport 1 (p.map FreeLoop.constants.continuous) (circleCurryFreeGenLoop 1 x Γ)⟧ :=
      Quotient.sound (circleCurryFreeGenLoop_transport_homotopic 1 p Γ)
    exact (piThreeFreeLoopPiTwoMulEquiv_mk y (genLoopTransport 2 p Γ)).trans
      (hc.trans (congrArg (homotopyGroupTransport 1 (p.map FreeLoop.constants.continuous))
        (piThreeFreeLoopPiTwoMulEquiv_mk x Γ)).symm)


theorem freeLoopContractiblePiTwoMulEquiv_transport [SimplyConnectedSpace Q]
    (p : Path x y) (a : HomotopyGroup (Fin 2) (freeLoop Q) (FreeLoop.constants x)) :
    freeLoopContractiblePiTwoMulEquiv y
      (homotopyGroupTransport 1 (p.map FreeLoop.constants.continuous) a) =
      homotopyGroupTransport 1 (p.map ContractibleLoop.constants.continuous)
        (freeLoopContractiblePiTwoMulEquiv x a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    let f : C(freeLoop Q, contractibleLoop Q) :=
      ⟨(contractibleLoopHomeomorphFreeLoop Q).symm,
        (contractibleLoopHomeomorphFreeLoop Q).symm.continuous⟩
    exact congrArg (fun r : GenLoop (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants y) =>
      (⟦r⟧ : HomotopyGroup (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants y)))
      (genLoopTransport_natural 1 f (p.map FreeLoop.constants.continuous) Γ).symm



theorem piThreeContractibleLoopPiTwoMulEquiv_transport [SimplyConnectedSpace Q]
    (p : Path x y) [Subsingleton (HomotopyGroup (Fin 2) Q x)]
    [Subsingleton (HomotopyGroup (Fin 2) Q y)] (a : HomotopyGroup (Fin 3) Q x) :
    piThreeContractibleLoopPiTwoMulEquiv y (homotopyGroupTransport 2 p a) =
      homotopyGroupTransport 1 (p.map ContractibleLoop.constants.continuous)
        (piThreeContractibleLoopPiTwoMulEquiv x a) := by
  change freeLoopContractiblePiTwoMulEquiv y
    (piThreeFreeLoopPiTwoMulEquiv y (homotopyGroupTransport 2 p a)) = _
  rw [piThreeFreeLoopPiTwoMulEquiv_transport, freeLoopContractiblePiTwoMulEquiv_transport]
  rfl




theorem piThreeLoopFamilyEquiv_transport [SimplyConnectedSpace Q]
    (p : Path x y) [Subsingleton (HomotopyGroup (Fin 2) Q x)]
    [Subsingleton (HomotopyGroup (Fin 2) Q y)] (a : HomotopyGroup (Fin 3) Q x) :
    piThreeLoopFamilyEquiv y (homotopyGroupTransport 2 p a) = piThreeLoopFamilyEquiv x a := by
  change homotopyGroupToFreeSphere 1 (ContractibleLoop.constants y)
    (piThreeContractibleLoopPiTwoMulEquiv y (homotopyGroupTransport 2 p a)) = _
  rw [piThreeContractibleLoopPiTwoMulEquiv_transport]
  exact homotopyGroupToFreeSphere_transport 1 (p.map ContractibleLoop.constants.continuous)
    (piThreeContractibleLoopPiTwoMulEquiv x a)

end DifferentialGeometry.Topology
