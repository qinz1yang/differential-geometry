import DifferentialGeometry.Topology.LoopSpace.BasedAdjunction



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]


def genLoopCircleUncurry (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p)) :
    GenLoop (K ⊕ Fin 1) P p :=
  GenLoop.genLoopGenLoopEquiv p
    (genLoopBasedMap ⟨(genLoopCircleHomeomorph p).symm,
      (genLoopCircleHomeomorph p).symm.continuous⟩
      (basedCircleConstant p) GenLoop.const (genLoopCircleHomeomorph_symm_constant p) Γ)



theorem genLoopCircleUncurry_apply (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p))
    (t : K ⊕ Fin 1 → unitInterval) :
    genLoopCircleUncurry p Γ t =
      (Γ (t ∘ Sum.inl)).val ((t (Sum.inr 0)).val : loopCircle) := rfl


theorem basedCirclePostcompose_constant (f : C(P, Q)) (p : P) :
    basedCirclePostcompose f p (basedCircleConstant p) = basedCircleConstant (f p) := rfl


theorem genLoopCircleUncurry_natural (f : C(P, Q)) (p : P)
    (Γ : GenLoop K (basedCircleLoop p) (basedCircleConstant p)) :
    genLoopCircleUncurry (f p)
      (genLoopBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) Γ) =
      genLoopPostcompose f p (genLoopCircleUncurry p Γ) := by
  ext t
  rfl



theorem basedCircleHomotopyGroupMulEquiv_mk (n : ℕ) (p : P)
    (Γ : GenLoop (Fin (n + 1)) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleHomotopyGroupMulEquiv n p ⟦Γ⟧ = ⟦genLoopCircleUncurry p Γ⟧ := rfl



theorem basedCircleHomotopyGroupMulEquiv_natural (n : ℕ) (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin (n + 1)) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleHomotopyGroupMulEquiv n (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupMap f p (basedCircleHomotopyGroupMulEquiv n p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg
      (fun r : GenLoop (Fin (n + 1) ⊕ Fin 1) Q (f p) =>
        (⟦r⟧ : HomotopyGroup (Fin (n + 1) ⊕ Fin 1) Q (f p)))
      (genLoopCircleUncurry_natural f p Γ)


theorem basedCirclePiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin 2) (basedCircleLoop p) (basedCircleConstant p)) :
    basedCirclePiTwoMulEquiv (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupMap f p (basedCirclePiTwoMulEquiv p a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    apply congrArg (fun r : GenLoop (Fin 3) Q (f p) => (⟦r⟧ : HomotopyGroup (Fin 3) Q (f p)))
    ext t
    rfl

end DifferentialGeometry.Topology
