import DifferentialGeometry.Topology.Connected.Frontier

open Set

namespace DifferentialGeometry.Topology

theorem pairwise_disjoint_interiors_of_frontier_chain
    {X : Type*} [TopologicalSpace X] (A S : ℕ → Set X)
    (hreg : ∀ n, closure (interior (A n)) = A n)
    (hconn : ∀ n, IsPreconnected (interior (A n)))
    (hfront : ∀ n, frontier (A n) = S n ∪ S (n + 1))
    (hne : ∀ n, (S n).Nonempty) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsep : ∀ i j, i + 1 < j → Disjoint (A i) (A j)) :
    Pairwise (fun i j => Disjoint (interior (A (i + 1))) (interior (A (j + 1)))) := by
  have hclosed (n : ℕ) : IsClosed (A n) := hreg n ▸ isClosed_closure
  have hleft (n : ℕ) : S n ⊆ A n := by
    apply Subset.trans _ (hclosed n).frontier_subset
    rw [hfront]
    exact subset_union_left
  have hright (n : ℕ) : S (n + 1) ⊆ A n := by
    apply Subset.trans _ (hclosed n).frontier_subset
    rw [hfront]
    exact subset_union_right
  have hadj (n : ℕ) : Disjoint (interior (A (n + 1))) (interior (A (n + 2))) := by
    have hAB : Disjoint (interior (A (n + 1))) (frontier (A (n + 2))) := by
      rw [hfront, disjoint_union_right]
      constructor
      · apply disjoint_interior_frontier.mono_right
        rw [hfront]
        exact subset_union_right
      · exact (hsep (n + 1) (n + 2 + 1) (by omega)).mono interior_subset (hleft _)
    have hBA : Disjoint (interior (A (n + 2))) (frontier (A (n + 1))) := by
      rw [hfront, disjoint_union_right]
      constructor
      · exact (hsep n (n + 2) (by omega)).symm.mono interior_subset (hright _)
      · apply disjoint_interior_frontier.mono_right
        rw [hfront]
        exact subset_union_left
    by_contra h
    have heq := eq_of_closure_interior_eq_of_disjoint_interior_frontier
      (hreg (n + 1)) (hreg (n + 2)) (hconn (n + 1)) (hconn (n + 2))
      hAB hBA (Set.not_disjoint_iff.mp h)
    obtain ⟨x, hx⟩ := hne (n + 1)
    have hxfront : x ∈ frontier (A (n + 1)) := by
      rw [hfront]
      exact Or.inl hx
    rw [heq, hfront] at hxfront
    rcases hxfront with hx' | hx'
    · exact Set.disjoint_left.mp (hS (by omega : n + 1 ≠ n + 2)) hx hx'
    · exact Set.disjoint_left.mp (hS (by omega : n + 1 ≠ n + 2 + 1)) hx hx'
  have hlt (i j : ℕ) (hij : i < j) :
      Disjoint (interior (A (i + 1))) (interior (A (j + 1))) := by
    by_cases h : j = i + 1
    · subst j
      simpa only [Nat.add_assoc] using hadj i
    · exact (hsep (i + 1) (j + 1) (by omega)).mono interior_subset interior_subset
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

theorem inter_succ_eq_of_frontier_chain
    {X : Type*} [TopologicalSpace X] (A S : ℕ → Set X)
    (hreg : ∀ n, closure (interior (A n)) = A n)
    (hconn : ∀ n, IsPreconnected (interior (A n)))
    (hfront : ∀ n, frontier (A n) = S n ∪ S (n + 1))
    (hne : ∀ n, (S n).Nonempty) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hsep : ∀ i j, i + 1 < j → Disjoint (A i) (A j)) :
    ∀ n, A (n + 1) ∩ A (n + 2) = S (n + 2) := by
  have hd := pairwise_disjoint_interiors_of_frontier_chain A S hreg hconn hfront hne hS hsep
  intro n
  have hdn : Disjoint (interior (A (n + 1))) (interior (A (n + 2))) := by
    simpa only [Nat.add_assoc] using hd (by omega : n ≠ n + 1)
  have hleft := hdn.closure_right isOpen_interior
  rw [hreg] at hleft
  have hright := hdn.closure_left isOpen_interior
  rw [hreg] at hright
  have hclosed (n : ℕ) : IsClosed (A n) := hreg n ▸ isClosed_closure
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    have hf : x ∈ frontier (A (n + 1)) :=
      ⟨subset_closure hx, fun hi => Set.disjoint_left.mp hleft hi hx'⟩
    have hf' : x ∈ frontier (A (n + 2)) :=
      ⟨subset_closure hx', fun hi => Set.disjoint_left.mp hright hx hi⟩
    rw [hfront] at hf hf'
    rcases hf with hf | hf
    · rcases hf' with hf' | hf'
      · exact hf'
      · exact False.elim (Set.disjoint_left.mp (hS (by omega : n + 1 ≠ n + 2 + 1)) hf hf')
    · simpa only [Nat.add_assoc] using hf
  · intro hx
    constructor
    · apply (hclosed (n + 1)).frontier_subset
      rw [hfront]
      exact Or.inr (by simpa only [Nat.add_assoc] using hx)
    · apply (hclosed (n + 2)).frontier_subset
      rw [hfront]
      exact Or.inl hx

end DifferentialGeometry.Topology
