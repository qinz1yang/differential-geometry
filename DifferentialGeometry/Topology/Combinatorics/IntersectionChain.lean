import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology

theorem exists_chain_with_disjoint_nonadjacent_of_intersection_reachable
    {X ι : Type*} (T : ι → Set X) {a b : ι}
    (h : Relation.ReflTransGen (fun i j => (T i ∩ T j).Nonempty) a b) :
    ∃ n : ℕ, ∃ f : Fin (n + 1) → ι,
      f 0 = a ∧ f (Fin.last n) = b ∧ Function.Injective f ∧
      (∀ i : Fin n, (T (f i.castSucc) ∩ T (f i.succ)).Nonempty) ∧
      ∀ i j : Fin (n + 1), i.val + 1 < j.val → Disjoint (T (f i)) (T (f j)) := by
  let G : SimpleGraph ι := {
    Adj := fun i j => i ≠ j ∧ (T i ∩ T j).Nonempty
    symm := ⟨fun i j hij => ⟨hij.1.symm, by simpa only [inter_comm] using hij.2⟩⟩
    loopless := ⟨fun i h => h.1 rfl⟩ }
  have hab : G.Reachable a b := by
    induction h with
    | refl => exact SimpleGraph.Reachable.refl a
    | @tail b c hab hbc ih =>
      by_cases hne : b = c
      · exact hne ▸ ih
      · exact ih.trans (SimpleGraph.Adj.reachable (G := G) ⟨hne, hbc⟩)
  obtain ⟨p, hp⟩ := hab.exists_walk_length_eq_dist
  have hpath := p.isPath_of_length_eq_dist hp
  let f : Fin (p.length + 1) → ι := fun i => p.getVert i.val
  refine ⟨p.length, f, p.getVert_zero, p.getVert_length, ?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext (hpath.getVert_injOn (by simpa using Nat.le_of_lt_succ i.isLt)
      (by simpa using Nat.le_of_lt_succ j.isLt) hij)
  · intro i
    exact (p.adj_getVert_succ i.isLt).2
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hne : p.getVert i.val ≠ p.getVert j.val := by
      intro heq
      have := hpath.getVert_injOn (by simpa using Nat.le_of_lt_succ i.isLt)
        (by simpa using Nat.le_of_lt_succ j.isLt) heq
      omega
    have hadj : G.Adj (p.getVert i.val) (p.getVert j.val) := ⟨hne, x, hxi, hxj⟩
    have hshort := SimpleGraph.dist_le ((p.take i.val).append ((p.drop j.val).cons hadj))
    rw [← hp, SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.drop_length] at hshort
    have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ p.length := Nat.le_of_lt_succ j.isLt
    omega

end DifferentialGeometry.Topology
