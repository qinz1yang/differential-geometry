import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Order.Filter.Cofinite

open Set Filter

namespace LocallyFinite

theorem frontier_iUnion_subset {X ι : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hs : LocallyFinite s) :
    frontier (⋃ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  have hc := hx.1
  rw [hs.closure_iUnion] at hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  exact mem_iUnion.mpr ⟨i, hi, fun h => hx.2 (interior_mono (subset_iUnion s i) h)⟩

theorem frontier_iUnion_succ_eq_of_chain {X : Type*} [TopologicalSpace X]
    {A : ℕ → Set X} (hA : LocallyFinite A) (S : ℕ → Set X)
    (hclosed : ∀ n, IsClosed (A n))
    (hfront : ∀ n, frontier (A n) = S n ∪ S (n + 1))
    (hseam : ∀ n, S (n + 2) ⊆ interior (A (n + 1) ∪ A (n + 2)))
    (hsep : ∀ n, Disjoint (A 0) (A (n + 2))) :
    frontier (⋃ n, A (n + 1)) = S 1 := by
  have htail := hA.comp_injective (g := fun n : ℕ => n + 1) (fun _ _ hij => Nat.add_right_cancel hij)
  have hrest := hA.comp_injective (g := fun n : ℕ => n + 2) (fun _ _ hij => Nat.add_right_cancel hij)
  have hrestClosed := hrest.isClosed_iUnion (fun n => hclosed (n + 2))
  have hglued (n : ℕ) : S (n + 2) ⊆ interior (⋃ k, A (k + 1)) := by
    apply (hseam n).trans (interior_mono _)
    exact union_subset (subset_iUnion (fun k => A (k + 1)) n)
      (subset_iUnion (fun k => A (k + 1)) (n + 1))
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (htail.frontier_iUnion_subset hx)
    change x ∈ frontier (A (n + 1)) at hn
    rw [hfront] at hn
    rcases hn with hn | hn
    · cases n with
      | zero => exact hn
      | succ n => exact False.elim (hx.2 (hglued n hn))
    · exact False.elim (hx.2 (hglued n hn))
  · intro hx
    have hxA₀ : x ∈ A 0 := (hclosed 0).frontier_subset
      ((hfront 0).symm ▸ Or.inr hx)
    have hxfront : x ∈ frontier (A 1) := (hfront 1).symm ▸ Or.inl hx
    have hxrest : x ∉ ⋃ n, A (n + 2) := by
      intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hsep n) hxA₀ hn
    refine ⟨subset_closure (mem_iUnion.mpr ⟨0, (hclosed 1).frontier_subset hxfront⟩), ?_⟩
    intro hi
    apply hxfront.2
    apply mem_interior.mpr
    refine ⟨interior (⋃ n, A (n + 1)) ∩ (⋃ n, A (n + 2))ᶜ, ?_,
      isOpen_interior.inter hrestClosed.isOpen_compl, hi, hxrest⟩
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp (interior_subset hy.1)
    cases n with
    | zero => exact hn
    | succ n => exact False.elim (hy.2 (mem_iUnion.mpr ⟨n, hn⟩))

theorem eventually_subset_interior_of_isCompact_frontier
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} (hA : LocallyFinite A)
    {U : Set X} (hfront : IsCompact (frontier U))
    (hconn : ∀ᶠ i in cofinite, IsPreconnected (A i))
    (hmeet : ∀ᶠ i in cofinite, (A i ∩ interior U).Nonempty) :
    ∀ᶠ i in cofinite, A i ⊆ interior U := by
  have hdisj : ∀ᶠ i in cofinite, Disjoint (A i) (frontier U) := by
    apply Filter.eventually_cofinite.mpr
    apply (hA.finite_nonempty_inter_compact hfront).subset
    intro i hi
    exact Set.not_disjoint_iff.mp hi
  filter_upwards [hconn, hdisj, hmeet] with i hc hd hm
  exact DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier hc hd hm

end LocallyFinite
