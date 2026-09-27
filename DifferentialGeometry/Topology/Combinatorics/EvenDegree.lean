/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card

open Set

namespace DifferentialGeometry.Topology.Combinatorics

variable {V : Type*}

theorem even_neighborSet_ncard_of_forall_ne (G : SimpleGraph V) [Finite V] (p : V)
    (h : ∀ v, v ≠ p → Even (G.neighborSet v).ncard) : Even (G.neighborSet p).ncard := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  by_contra hp
  have hpodd : Odd (G.degree p) := by
    rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact Nat.not_even_iff_odd.mp hp
  obtain ⟨v, hvp, hvodd⟩ := G.exists_ne_odd_degree_of_exists_odd_degree p hpodd
  rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hvodd
  exact (Nat.not_even_iff_odd.mpr hvodd) (h v hvp)

theorem not_isBridge_of_even_neighborSet_ncard (G : SimpleGraph V) [Finite V]
    (h : ∀ v, Even (G.neighborSet v).ncard) {u v : V} (huv : G.Adj u v) :
    ¬ G.IsBridge s(u, v) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  intro hbridge
  let D := G.deleteEdges {s(u, v)}
  let c := D.connectedComponentMk u
  have huC : u ∈ c.supp := rfl
  have hvC : v ∉ c.supp := by
    intro hv
    exact hbridge (c.reachable_of_mem_supp huC hv)
  let H := D.induce c.supp
  let a : c.supp := ⟨u, huC⟩
  have hdegree (x : c.supp) : H.degree x = (D.neighborSet (x : V)).ncard := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset]
    · rw [← D.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    · intro y hy
      exact c.mem_supp_of_adj_mem_supp x.2 hy
  have hDother (x : c.supp) (hxu : (x : V) ≠ u) :
      D.neighborSet (x : V) = G.neighborSet (x : V) := by
    have hxv : (x : V) ≠ v := fun h => hvC (h ▸ x.2)
    ext y
    simp only [D, SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj, mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hxy
      refine ⟨hxy, ?_⟩
      intro he
      rcases Sym2.eq_iff.mp he with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hxu hx
      · exact hxv hx
  have hDa : D.neighborSet u = G.neighborSet u \ {v} := by
    ext y
    simp only [D, SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj, mem_sdiff,
      mem_singleton_iff, Sym2.eq_iff, true_and]
    constructor
    · rintro ⟨huy, hne⟩
      exact ⟨huy, fun h => hne (Or.inl h)⟩
    · rintro ⟨huy, hne⟩
      exact ⟨huy, fun he => he.elim hne (fun he => huv.ne he.1)⟩
  have haodd : Odd (H.degree a) := by
    rw [hdegree, hDa, Set.ncard_sdiff_singleton_of_mem (show v ∈ G.neighborSet u from huv)]
    obtain ⟨k, hk⟩ := h u
    have hpos : 0 < (G.neighborSet u).ncard := Nat.pos_of_ne_zero (Set.ncard_ne_zero_of_mem (show v
        ∈ G.neighborSet u from huv))
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨b, hba, hbodd⟩ := H.exists_ne_odd_degree_of_exists_odd_degree a haodd
  have hbu : (b : V) ≠ u := fun hb => hba (Subtype.ext hb)
  rw [hdegree, hDother b hbu] at hbodd
  exact (Nat.not_even_iff_odd.mpr hbodd) (h b)

theorem exists_cycle_of_adj_of_even_neighborSet_ncard (G : SimpleGraph V) [Finite V]
    (h : ∀ v, Even (G.neighborSet v).ncard) {u v : V} (huv : G.Adj u v) :
    ∃ (w : V) (p : G.Walk w w), p.IsCycle ∧ s(u, v) ∈ p.edges := by
  apply SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
  exact ⟨huv, not_not.mp (not_isBridge_of_even_neighborSet_ncard G h huv)⟩

theorem exists_cycle_of_adj_of_neighborSet_ncard_eq_two_except (G : SimpleGraph V) [Finite V]
    (p : V) (h : ∀ v, v ≠ p → (G.neighborSet v).ncard = 2) {u v : V} (huv : G.Adj u v) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ s(u, v) ∈ q.edges := by
  have heven : ∀ v, v ≠ p → Even (G.neighborSet v).ncard := by
    intro v hv
    rw [h v hv]
    exact ⟨1, rfl⟩
  apply exists_cycle_of_adj_of_even_neighborSet_ncard G (fun v => ?_) huv
  by_cases hv : v = p
  · exact hv ▸ even_neighborSet_ncard_of_forall_ne G p heven
  · exact heven v hv

end DifferentialGeometry.Topology.Combinatorics
