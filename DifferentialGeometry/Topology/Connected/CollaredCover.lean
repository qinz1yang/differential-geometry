/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import DifferentialGeometry.Topology.VanKampen.BoundaryCollarOrientation

open Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e)

theorem exists_open_cover_of_closed_cover [ConnectedSpace S] {P Q : Set X}
    (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q) :
    ∃ d : TwoSidedCollar e, d.range ⊆ c.range ∧
      (∀ p : S × ℝ, d.toFun p ∈ P ↔ p.2 ≤ 0) ∧
      (∀ p : S × ℝ, d.reverse.toFun p ∈ Q ↔ p.2 ≤ 0) ∧
      d.domainNeighborhood P ∪ d.reverse.domainNeighborhood Q = univ ∧
      d.domainNeighborhood P ∩ d.reverse.domainNeighborhood Q = d.range := by
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hQP : Q ∪ P = univ := (union_comm Q P).trans hcover
  have hPi := interior_eq_compl_of_closure_sdiff_eq hcover hQcl
  have hQi := interior_eq_compl_of_closure_sdiff_eq hQP hPcl
  have hPf : frontier P = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet
  have hQf : frontier Q = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hQP hQcl hPcl).trans
      ((inter_comm Q P).trans hmeet)
  obtain ⟨d, hdc, hdP⟩ := c.exists_outward_collar_of_frontier_zero
    (closure_interior_eq_of_closure_sdiff_eq hcover hPcl hQcl)
    (c.frontier_zero_of_disjoint_rest (hPf.trans (union_empty _).symm) (disjoint_empty _))
  have hdQ (p : S × ℝ) : d.toFun p ∈ Q ↔ 0 ≤ p.2 := by
    constructor
    · intro hp
      by_contra ht
      have hpP := (hdP p).mpr (le_of_lt (lt_of_not_ge ht))
      have hzero := (d.frontier_zero_of_disjoint_rest
        (hPf.trans (union_empty _).symm) (disjoint_empty _) p).mp
          (hPf.symm ▸ hmeet.subset ⟨hpP, hp⟩)
      exact (ne_of_lt (lt_of_not_ge ht)) hzero
    · intro ht
      rcases eq_or_lt_of_le ht with he | hp
      · have heq : d.toFun p = e p.1 := by
          rw [show p = (p.1, 0) from Prod.ext rfl he.symm, d.zero_eq]
        exact hmeet.symm.subset ⟨p.1, heq.symm⟩ |>.2
      · exact (hcover.symm ▸ mem_univ (d.toFun p) : d.toFun p ∈ P ∪ Q).resolve_left
          (fun h => (not_le_of_gt hp) ((hdP p).mp h))
  have hdrQ (p : S × ℝ) : d.reverse.toFun p ∈ Q ↔ p.2 ≤ 0 := by
    change d.toFun (p.1, -p.2) ∈ Q ↔ p.2 ≤ 0
    rw [hdQ]
    exact neg_nonneg
  have hrange : d.reverse.range = d.range := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p.1, -p.2), rfl⟩
    · rintro ⟨p, rfl⟩
      refine ⟨(p.1, -p.2), ?_⟩
      change d.toFun (p.1, - -p.2) = d.toFun p
      simp only [neg_neg]
  let U := d.domainNeighborhood P
  let V := d.reverse.domainNeighborhood Q
  have hUV : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    rcases (hcover.symm ▸ mem_univ x : x ∈ P ∪ Q) with hp | hq
    · exact Or.inl (d.subset_domainNeighborhood hP hPf.subset hp)
    · exact Or.inr (d.reverse.subset_domainNeighborhood hQ hQf.subset hq)
  have hUVinter : U ∩ V = d.range := by
    change (interior P ∪ d.range) ∩ (interior Q ∪ d.reverse.range) = d.range
    rw [hrange, hPi, hQi]
    ext x
    constructor
    · rintro ⟨hp | hr, hq | hr⟩
      · exact False.elim ((hcover.symm ▸ mem_univ x : x ∈ P ∪ Q).elim hq hp)
      · exact hr
      · exact hr
      · exact hr
    · intro hr
      exact ⟨Or.inr hr, Or.inr hr⟩
  exact ⟨d, hdc, hdP, hdrQ, hUV, hUVinter⟩

theorem domainNeighborhood_eq_union {K : Set X} (hK : IsClosed K)
    (hfront : frontier K ⊆ Set.range e) : c.domainNeighborhood K = K ∪ c.range := by
  apply Set.Subset.antisymm
  · exact union_subset_union interior_subset subset_rfl
  · exact union_subset (c.subset_domainNeighborhood hK hfront) subset_union_right

theorem isConnected_domainNeighborhood [ConnectedSpace S] {K : Set X}
    (hK : IsClosed K) (hKc : IsConnected K) (hfront : frontier K ⊆ Set.range e)
    (hzero : Set.range e ⊆ K) : IsConnected (c.domainNeighborhood K) := by
  classical
  rw [c.domainNeighborhood_eq_union hK hfront]
  have hR : IsConnected c.range := isConnected_range c.isOpenEmbedding_toFun.continuous
  let s := Classical.arbitrary S
  exact hKc.union ⟨e s, hzero ⟨s, rfl⟩, ⟨(s, 0), c.zero_eq s⟩⟩ hR

include c in
theorem pathConnectedSpace_left_of_closed_cover
    [ConnectedSpace S] [ConnectedSpace X] [LocallyPathConnectedSpace X] {P Q : Set X}
    (hcover : P ∪ Q = univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q) : PathConnectedSpace P := by
  classical
  have hP : IsClosed P := hPcl ▸ isClosed_closure
  have hQ : IsClosed Q := hQcl ▸ isClosed_closure
  have hPf : frontier P = Set.range e :=
    (frontier_eq_inter_of_closure_sdiff_eq hcover hPcl hQcl).trans hmeet
  have hzero : Set.range e ⊆ P := hmeet.symm.subset.trans inter_subset_left
  have hPc : IsConnected P := ⟨⟨e (Classical.arbitrary S), hzero ⟨_, rfl⟩⟩,
    isPreconnected_left_of_isClosed_union hP hQ (hcover.symm ▸ isPreconnected_univ)
      (hmeet.symm ▸ (isConnected_range c.continuous_e).isPreconnected)⟩
  obtain ⟨d, _, hdP, _, _, _⟩ := c.exists_open_cover_of_closed_cover hcover hmeet hPcl hQcl
  let _ : PathConnectedSpace (d.domainNeighborhood P) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((d.isOpen_domainNeighborhood P).isConnected_iff_isPathConnected.mp
        (d.isConnected_domainNeighborhood hP hPc hPf.subset hzero))
  exact (d.domainRetraction_leftInverse hP hPf.subset hdP).surjective.pathConnectedSpace
    (d.domainRetraction hdP).continuous

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
