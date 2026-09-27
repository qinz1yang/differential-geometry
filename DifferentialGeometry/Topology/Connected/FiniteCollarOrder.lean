import DifferentialGeometry.Topology.Embedding.Frontier
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.OrderedSeparatingCollars
import Mathlib.Data.Fin.SuccPredOrder

open Set Filter Topology

namespace DifferentialGeometry.Topology

theorem separator_subset_lower_side_of_finite_chain
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (T : Fin (n + 1) → Set Y) (hT : ∀ k, IsPreconnected (T k))
    (hmeet : ∀ k : Fin n, (T k.castSucc ∩ T k.succ).Nonempty)
    (hdisj : ∀ k l : Fin (n + 1), k.val + 1 < l.val → Disjoint (T k) (T l))
    (P K Q : Fin n → Set X)
    (hP : ∀ j, IsClosed (P j)) (hK : ∀ j, IsClosed (K j)) (hQ : ∀ j, IsClosed (Q j))
    (hcover : ∀ j, P j ∪ K j ∪ Q j = univ) (hPQ : ∀ j, Disjoint (P j) (Q j))
    (hKT : ∀ j, f '' K j ⊆ T j.castSucc ∩ T j.succ)
    (Sminus Splus : Set X)
    (hboundary : frontier (range f) ⊆ f '' Sminus ∪ f '' Splus)
    (hlower : ∀ j, Sminus ⊆ P j)
    (hfirst : f '' Sminus ⊆ T 0) (hlast : f '' Splus ⊆ T (Fin.last n))
    (hne : Sminus.Nonempty) :
    ∀ i j : Fin n, i < j → K i ⊆ P j := by
  have hfrontQ (j : Fin n) : frontier (Q j) ⊆ K j := by
    intro x hx
    have hxQ : x ∈ Q j := (hQ j).frontier_subset hx
    by_contra hxK
    have hxP : x ∉ P j := fun h ↦ Set.disjoint_left.mp (hPQ j) h hxQ
    have hsub : (P j ∪ K j)ᶜ ⊆ Q j := by
      intro y hy
      exact (show y ∈ P j ∪ K j ∪ Q j from (hcover j).symm ▸ mem_univ y).resolve_left hy
    have hnb : Q j ∈ 𝓝 x := Filter.mem_of_superset
      (((hP j).union (hK j)).isOpen_compl.mem_nhds (not_or.mpr ⟨hxP, hxK⟩)) hsub
    exact hx.2 (mem_interior_iff_mem_nhds.mpr hnb)
  have hclosedQ (j : Fin n) : IsClosed (f '' Q j) := hf.isClosedMap _ (hQ j)
  have hfrontImageQ (j : Fin n) :
      frontier (f '' Q j) ⊆ f '' K j ∪ f '' Splus := by
    intro y hy
    rcases Embedding.frontier_image_subset_of_isEmbedding hf.isEmbedding (Q j) hy with hr | hq
    · rcases hboundary hr with ⟨x, hx, hxy⟩ | hp
      · obtain ⟨z, hz, hzy⟩ := (hclosedQ j).frontier_subset hy
        have hxz : x = z := hf.injective (hxy.trans hzy.symm)
        exact False.elim (Set.disjoint_left.mp (hPQ j) (hlower j hx) (hxz.symm ▸ hz))
      · exact Or.inr hp
    · obtain ⟨x, hx, hxy⟩ := hq
      exact Or.inl ⟨x, hfrontQ j hx, hxy⟩
  intro i j hij
  let B : Set Y := ⋃ k ∈ Iic i.castSucc, T k
  have hB : IsPreconnected B := by
    apply IsPreconnected.biUnion_of_chain ordConnected_Iic (fun k _ ↦ hT k)
    intro k hk _
    have hneLast : k ≠ Fin.last n := by
      intro heq
      have hv : k.val ≤ i.val := hk
      rw [heq, Fin.val_last] at hv
      exact (not_le_of_gt i.isLt) hv
    obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hneLast
    simpa only [Fin.orderSucc_castSucc] using hmeet k
  have hBK : Disjoint B (f '' K j) := by
    apply Set.disjoint_left.mpr
    intro y hyB hyK
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hyB
    have hki : k.val ≤ i.val := hk
    have hijv : i.val < j.val := hij
    have hgap : k.val + 1 < j.succ.val := by
      change k.val + 1 < j.val + 1
      omega
    exact Set.disjoint_left.mp (hdisj k j.succ hgap) hyk (hKT j hyK).2
  have hBplus : Disjoint B (f '' Splus) := by
    apply Set.disjoint_left.mpr
    intro y hyB hyS
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hyB
    have hki : k.val ≤ i.val := hk
    have hijv : i.val < j.val := hij
    have hgap : k.val + 1 < (Fin.last n).val := by
      change k.val + 1 < n
      omega
    exact Set.disjoint_left.mp (hdisj k (Fin.last n) hgap) hyk (hlast hyS)
  have havoid : Disjoint B (frontier ((f '' Q j)ᶜ)) := by
    rw [frontier_compl]
    apply Set.disjoint_left.mpr
    intro y hyB hyfront
    rcases hfrontImageQ j hyfront with hyK | hyS
    · exact Set.disjoint_left.mp hBK hyB hyK
    · exact Set.disjoint_left.mp hBplus hyB hyS
  have htouch : (B ∩ interior ((f '' Q j)ᶜ)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have hxB : f x ∈ B := mem_iUnion₂.mpr
      ⟨0, Fin.zero_le _, hfirst ⟨x, hx, rfl⟩⟩
    have hxQ : f x ∉ f '' Q j := by
      rintro ⟨y, hy, hyx⟩
      have heq := hf.injective hyx
      exact Set.disjoint_left.mp (hPQ j) (hlower j hx) (heq ▸ hy)
    exact ⟨f x, hxB, (hclosedQ j).isOpen_compl.interior_eq.symm ▸ hxQ⟩
  have hBoutside : B ⊆ interior ((f '' Q j)ᶜ) :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hB havoid htouch
  intro x hx
  have hxB : f x ∈ B := mem_iUnion₂.mpr
    ⟨i.castSucc, (show i.castSucc ≤ i.castSucc from le_rfl), (hKT i ⟨x, hx, rfl⟩).1⟩
  rcases (show x ∈ P j ∪ K j ∪ Q j from (hcover j).symm ▸ mem_univ x) with (hp | hk) | hq
  · exact hp
  · exact False.elim (Set.disjoint_left.mp hBK hxB ⟨x, hk, rfl⟩)
  · exact False.elim (interior_subset (hBoutside hxB) ⟨x, hq, rfl⟩)

theorem ordered_exteriors_of_finite_chain
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y] {n : ℕ}
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (T : Fin (n + 1) → Set Y) (hT : ∀ k, IsPreconnected (T k))
    (hmeet : ∀ k : Fin n, (T k.castSucc ∩ T k.succ).Nonempty)
    (hdisj : ∀ k l : Fin (n + 1), k.val + 1 < l.val → Disjoint (T k) (T l))
    (P K Q : Fin n → Set X)
    (hP : ∀ j, IsClosed (P j)) (hK : ∀ j, IsClosed (K j)) (hQ : ∀ j, IsClosed (Q j))
    (hcover : ∀ j, P j ∪ K j ∪ Q j = univ) (hPQ : ∀ j, Disjoint (P j) (Q j))
    (hKT : ∀ j, f '' K j ⊆ T j.castSucc ∩ T j.succ)
    (Sminus Splus : Set X)
    (hboundary : frontier (range f) ⊆ f '' Sminus ∪ f '' Splus)
    (hlower : ∀ j, Sminus ⊆ P j) (hupper : ∀ j, Splus ⊆ Q j)
    (hfirst : f '' Sminus ⊆ T 0) (hlast : f '' Splus ⊆ T (Fin.last n))
    (hminus : Sminus.Nonempty) (hplus : Splus.Nonempty)
    (hconnK : ∀ j, IsPreconnected (K j)) (hconnQ : ∀ j, IsPreconnected (Q j)) :
    ∀ i j : Fin n, i < j →
      P i ∪ K i ⊆ interior (P j) ∧ K j ∪ Q j ⊆ interior (Q i) ∧
        interior (Q i) ∪ interior (P j) = univ := by
  have horder := separator_subset_lower_side_of_finite_chain f hf T hT hmeet hdisj
    P K Q hP hK hQ hcover hPQ hKT Sminus Splus hboundary hlower hfirst hlast hminus
  have hattach (j : Fin n) : (K j ∩ Q j).Nonempty := by
    obtain ⟨xm, hxm⟩ := hminus
    obtain ⟨xp, hxp⟩ := hplus
    have hwhole : (univ : Set X) ⊆ (P j ∪ K j) ∪ Q j := by
      rw [hcover j]
    obtain ⟨x, _, hx, hxQ⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
      (P j ∪ K j) (Q j) ((hP j).union (hK j)) (hQ j) hwhole
      ⟨xm, mem_univ _, Or.inl (hlower j hxm)⟩ ⟨xp, mem_univ _, hupper j hxp⟩
    rcases hx with hxP | hxK
    · exact False.elim (Set.disjoint_left.mp (hPQ j) hxP hxQ)
    · exact ⟨x, hxK, hxQ⟩
  intro i j hij
  have hKK : Disjoint (K i) (K j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hgap : i.castSucc.val + 1 < j.succ.val := Nat.add_lt_add_right hij 1
    exact Set.disjoint_left.mp (hdisj i.castSucc j.succ hgap)
      (hKT i ⟨x, hxi, rfl⟩).1 (hKT j ⟨x, hxj, rfl⟩).2
  have hplace : (K i ∩ P j).Nonempty := by
    obtain ⟨x, hx, _⟩ := hattach i
    exact ⟨x, hx, horder i j hij hx⟩
  have hcommon : (Q i ∩ Q j).Nonempty := by
    obtain ⟨x, hx⟩ := hplus
    exact ⟨x, hupper i hx, hupper j hx⟩
  exact ordered_exteriors_of_disjoint_separating_collars
    (P i) (K i) (Q i) (P j) (K j) (Q j)
    (hP i) (hK i) (hQ i) (hP j) (hK j) (hQ j)
    (hcover i) (hcover j) (hPQ i) (hPQ j) hKK (hconnK i)
    (IsPreconnected.union' (hattach j) (hconnK j) (hconnQ j)) hplace hcommon

end DifferentialGeometry.Topology
