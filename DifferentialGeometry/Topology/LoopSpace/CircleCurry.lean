import DifferentialGeometry.Topology.LoopSpace.BasedAdjunctionNaturality



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q]


def cubeCircleCoordinates (n : ℕ) (v : Fin (n + 1) → unitInterval) (s : unitInterval) :
    Fin (n + 2) → unitInterval :=
  Sum.elim v (fun _ : Fin 1 => s) ∘ (finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)).symm


theorem continuous_cubeCircleCoordinates (n : ℕ) :
    Continuous (fun z : (Fin (n + 1) → unitInterval) × unitInterval =>
      cubeCircleCoordinates n z.1 z.2) := by
  apply continuous_pi
  intro i
  unfold cubeCircleCoordinates
  simp only [Function.comp_apply]
  cases (finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)).symm i with
  | inl j => exact (continuous_apply j).comp continuous_fst
  | inr j => exact continuous_snd


theorem cubeCircleCoordinates_boundary (n : ℕ) (v : Fin (n + 1) → unitInterval)
    (hv : v ∈ Cube.boundary (Fin (n + 1))) (s : unitInterval) :
    cubeCircleCoordinates n v s ∈ Cube.boundary (Fin (n + 2)) := by
  obtain ⟨i, hi⟩ := hv
  refine ⟨(finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)) (Sum.inl i), ?_⟩
  simpa only [cubeCircleCoordinates, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl] using hi


def genLoopCircleUncurryHomeomorph (n : ℕ) (q : Q) :
    GenLoop (Fin (n + 1)) (basedCircleLoop q) (basedCircleConstant q) ≃ₜ
      GenLoop (Fin (n + 2)) Q q :=
  ((genLoopBasedHomeomorph (genLoopCircleHomeomorph q).symm
    (basedCircleConstant q) GenLoop.const (genLoopCircleHomeomorph_symm_constant q)).trans
      (GenLoop.genLoopGenLoopEquiv q)).trans
        (GenLoop.congr q (finSumFinEquiv : Fin (n + 1) ⊕ Fin 1 ≃ Fin (n + 2)))


def genLoopCircleCurry (n : ℕ) (q : Q) (Γ : GenLoop (Fin (n + 2)) Q q) :
    GenLoop (Fin (n + 1)) (basedCircleLoop q) (basedCircleConstant q) :=
  (genLoopCircleUncurryHomeomorph n q).symm Γ



theorem genLoopCircleCurry_coe (n : ℕ) (q : Q) (Γ : GenLoop (Fin (n + 2)) Q q)
    (v : Fin (n + 1) → unitInterval) (s : unitInterval) :
    (genLoopCircleCurry n q Γ v).val (s.val : loopCircle) = Γ (cubeCircleCoordinates n v s) := by
  exact pathToCircle_coe _ s


theorem basedCirclePiTwoMulEquiv_uncurry_mk (q : Q)
    (Γ : GenLoop (Fin 2) (basedCircleLoop q) (basedCircleConstant q)) :
    basedCirclePiTwoMulEquiv q ⟦Γ⟧ = ⟦genLoopCircleUncurryHomeomorph 1 q Γ⟧ := rfl


theorem basedCirclePiTwoMulEquiv_symm_mk (q : Q) (Γ : GenLoop (Fin 3) Q q) :
    (basedCirclePiTwoMulEquiv q).symm ⟦Γ⟧ = ⟦genLoopCircleCurry 1 q Γ⟧ := by
  apply (basedCirclePiTwoMulEquiv q).injective
  have hr := (basedCirclePiTwoMulEquiv_uncurry_mk q (genLoopCircleCurry 1 q Γ)).trans
    (congrArg (fun r : GenLoop (Fin 3) Q q => (⟦r⟧ : HomotopyGroup (Fin 3) Q q))
      ((genLoopCircleUncurryHomeomorph 1 q).apply_symm_apply Γ))
  exact ((basedCirclePiTwoMulEquiv q).apply_symm_apply
    (⟦Γ⟧ : HomotopyGroup (Fin 3) Q q)).trans hr.symm

end DifferentialGeometry.Topology
