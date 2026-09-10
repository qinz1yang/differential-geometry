import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Data.Fin.Basic

open Set

namespace Poincare.Topology

theorem subset_of_frontier_subset_of_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {W U : Set X}
    (hU : IsClosed U) (hW : closure (interior W) = W)
    (hcW : IsPreconnected (interior W)) (hfrontier : frontier U ⊆ frontier W)
    (hmeet : (interior W ∩ interior U).Nonempty) : W ⊆ U := by
  have hdisj : Disjoint (interior W) (frontier U) :=
    disjoint_interior_frontier.mono_right hfrontier
  have hsubset := subset_interior_of_isPreconnected_of_disjoint_frontier hcW hdisj hmeet
  rw [← hW]
  exact (closure_mono (hsubset.trans interior_subset)).trans_eq hU.closure_eq

theorem subset_iUnion_of_frontier_sections
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (A : Fin n → Set X) (S : Fin (n + 1) → Set X) {W : Set X}
    (hA : ∀ i, IsClosed (A i))
    (hsections : ∀ i, frontier (A i) ⊆ S i.castSucc ∪ S i.succ)
    (hinternal : ∀ j, j ≠ 0 → j ≠ Fin.last n → S j ⊆ interior (⋃ i, A i))
    (hfirst : S 0 ⊆ frontier W) (hlast : S (Fin.last n) ⊆ frontier W)
    (hW : closure (interior W) = W) (hcW : IsPreconnected (interior W))
    (hmeet : (interior W ∩ interior (⋃ i, A i)).Nonempty) : W ⊆ ⋃ i, A i := by
  have hclosed : IsClosed (⋃ i, A i) := isClosed_iUnion_of_finite hA
  apply subset_of_frontier_subset_of_closure_interior_eq hclosed hW hcW _ hmeet
  intro x hx
  have hsection (j : Fin (n + 1)) (hj : x ∈ S j) : x ∈ frontier W := by
    by_cases hzero : j = 0
    · exact hfirst (hzero ▸ hj)
    by_cases hlast' : j = Fin.last n
    · exact hlast (hlast' ▸ hj)
    exact False.elim (hx.2 (hinternal j hzero hlast' hj))
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hclosed.frontier_subset hx)
  have hfi : x ∈ frontier (A i) := by
    refine ⟨subset_closure hi, ?_⟩
    intro hint
    exact hx.2 (interior_mono (subset_iUnion A i) hint)
  exact (hsections i hfi).elim (hsection i.castSucc) (hsection i.succ)

end Poincare.Topology
