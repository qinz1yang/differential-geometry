import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation
import Mathlib.Topology.Connected.Clopen

noncomputable section

open Set Topology

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

theorem compact_region_eq_of_frontier_eq
    {S X : Type*} [TopologicalSpace S] [ConnectedSpace S]
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {e : S → X} (c : TwoSidedCollar e)
    (hX : ¬ IsCompact (univ : Set X)) {A B : Set X}
    (hAc : IsCompact A) (hBc : IsCompact B)
    (hAr : closure (interior A) = A) (hBr : closure (interior B) = B)
    (hAi : IsPreconnected (interior A)) (hBi : IsPreconnected (interior B))
    (hfront : frontier A = Set.range e) (heq : frontier A = frontier B)
    (hside : ∀ p : S × ℝ, c.toFun p ∈ A ↔ p.2 ≤ 0) : A = B := by
  apply DifferentialGeometry.Topology.eq_of_frontier_eq_of_closure_interior_eq
    hAr hBr hAi hBi heq
  by_contra hdisj
  let N := c.toFun '' ((univ : Set S) ×ˢ Iio (0 : ℝ))
  let P := c.toFun '' ((univ : Set S) ×ˢ Ioi (0 : ℝ))
  have hNopen : IsOpen N :=
    c.isOpenEmbedding_toFun.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  have hNA : N ⊆ interior A := by
    apply interior_maximal _ hNopen
    rintro x ⟨p, hp, rfl⟩
    exact (hside p).mpr hp.2.le
  have hPconn : IsPreconnected P :=
    ((isConnected_univ.prod isConnected_Ioi).image _
      c.isOpenEmbedding_toFun.continuous.continuousOn).isPreconnected
  have havoid (p : S × ℝ) (hp : p.2 ≠ 0) : c.toFun p ∉ Set.range e := by
    rintro ⟨s, hs⟩
    have h := c.isOpenEmbedding_toFun.injective (hs.symm.trans (c.zero_eq s).symm)
    exact hp (congrArg Prod.snd h)
  have hPfront : Disjoint P (frontier B) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ hf
    exact havoid p hp.2.ne' ((heq.symm.trans hfront) ▸ hf)
  have hPmeet : (P ∩ interior B).Nonempty := by
    let s : S := Classical.arbitrary S
    have hsB : e s ∈ closure (interior B) := by
      rw [hBr]
      exact hBc.isClosed.frontier_subset ((heq.symm.trans hfront).symm ▸ mem_range_self s)
    obtain ⟨x, ⟨p, rfl⟩, hxB⟩ := mem_closure_iff.mp hsB c.range c.isOpen_range
      ⟨(s, 0), c.zero_eq s⟩
    have hp : 0 < p.2 := by
      by_contra hp
      rcases (le_of_not_gt hp).lt_or_eq with hn | hz
      · exact hdisj ⟨_, hNA ⟨p, ⟨mem_univ _, hn⟩, rfl⟩, hxB⟩
      · have hxF : c.toFun p ∈ frontier B := by
          rw [← heq, hfront]
          refine ⟨p.1, ?_⟩
          simpa only [← hz] using (c.zero_eq p.1).symm
        exact hxF.2 hxB
    exact ⟨_, ⟨p, ⟨mem_univ _, hp⟩, rfl⟩, hxB⟩
  have hPB : P ⊆ interior B :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hPconn hPfront hPmeet
  have hcover : c.range ⊆ A ∪ B := by
    rintro x ⟨p, rfl⟩
    by_cases hp : p.2 ≤ 0
    · exact Or.inl ((hside p).mpr hp)
    · exact Or.inr (interior_subset (hPB ⟨p, ⟨mem_univ _, lt_of_not_ge hp⟩, rfl⟩))
  have hopen : IsOpen (A ∪ B) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    by_cases hxAi : x ∈ interior A
    · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxAi)
        (interior_subset.trans subset_union_left)
    by_cases hxBi : x ∈ interior B
    · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hxBi)
        (interior_subset.trans subset_union_right)
    have hxF : x ∈ frontier A := by
      rcases hx with hxA | hxB
      · exact ⟨subset_closure hxA, hxAi⟩
      · rw [heq]
        exact ⟨subset_closure hxB, hxBi⟩
    obtain ⟨s, rfl⟩ := hfront ▸ hxF
    exact Filter.mem_of_superset
      (c.isOpen_range.mem_nhds ⟨(s, 0), c.zero_eq s⟩) hcover
  have hcompact : IsCompact (A ∪ B) := hAc.union hBc
  have hnonempty : (A ∪ B).Nonempty := by
    let s : S := Classical.arbitrary S
    exact ⟨e s, Or.inl (hAc.isClosed.frontier_subset (hfront.symm ▸ mem_range_self s))⟩
  have huniv : A ∪ B = univ :=
    (show IsClopen (A ∪ B) from ⟨hcompact.isClosed, hopen⟩).eq_univ hnonempty
  exact hX (huniv ▸ hcompact)

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
