import DifferentialGeometry.Topology.Homotopy.LoopTopology



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K N X : Type*} [TopologicalSpace X] [DecidableEq K] [DecidableEq N]


theorem genLoop_reindex_transAt (e : K ≃ N) (x : X) (i : K) (p q : GenLoop K X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  ext t
  change (GenLoop.transAt i p q) (t ∘ e) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy, Function.comp_apply]
  split_ifs
  · change p _ = p _
    exact congrArg p (update_comp_eq_of_injective t e.injective i _).symm
  · change q _ = q _
    exact congrArg q (update_comp_eq_of_injective t e.injective i _).symm


def homotopyGroupReindexMulEquiv [Nonempty K] [Nonempty N] (e : K ≃ N) (x : X) :
    HomotopyGroup K X x ≃* HomotopyGroup N X x where
  toEquiv := Quotient.congr (GenLoop.congr x e).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff (GenLoop.congr x e) p q).symm)
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : K := Classical.arbitrary K
        let E : HomotopyGroup K X x ≃ HomotopyGroup N X x :=
          Quotient.congr (GenLoop.congr x e).toEquiv
            (fun p q => (genLoopHomeomorph_homotopic_iff (GenLoop.congr x e) p q).symm)
        have hmul := congrArg E (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        exact (congrArg (fun r : GenLoop N X x => (⟦r⟧ : HomotopyGroup N X x))
          (genLoop_reindex_transAt e x i q p)).trans
            (HomotopyGroup.mul_spec (i := e i) (p := GenLoop.congr x e p) (q := GenLoop.congr x e q)).symm

end DifferentialGeometry.Topology
