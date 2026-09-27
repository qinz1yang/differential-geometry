/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_equiv_connectedComponents_of_finite_partition
    (K : Geometry.SimplicialComplex ℝ E) {ι : Type*} [Finite ι] (C : ι → Set E)
    (hC : ∀ i, IsConnected (C i)) (hclosed : ∀ i, IsClosed (C i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j)) (hcover : K.space = ⋃ i, C i) :
    ∃ e : ι ≃ ConnectedComponents K.space,
      ∀ i, (connectedComponentComplex K (e i)).space = C i := by
  classical
  choose p hp using fun i => (hC i).nonempty
  have hsub (i : ι) : C i ⊆ K.space := (subset_iUnion C i).trans hcover.symm.subset
  let f : ι → ConnectedComponents K.space := fun i =>
    ConnectedComponents.mk (⟨p i, hsub i (hp i)⟩ : K.space)
  have hf (i : ι) : (connectedComponentComplex K (f i)).space = C i := by
    dsimp only [f]
    rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
    let R := ⋃ j ∈ {j | j ≠ i}, C j
    have hRc : IsClosed R := (Set.toFinite _).isClosed_biUnion fun j _ => hclosed j
    have hCR : Disjoint (C i) R := disjoint_iUnion₂_right.mpr fun j hj => hdis (Ne.symm hj)
    have hcov : K.space ⊆ C i ∪ R := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.subset hx)
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hj⟩)
    apply Subset.antisymm ?_ ((hC i).isPreconnected.subset_connectedComponentIn (hp i) (hsub i))
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
      (C i) R (hclosed i) hRc ((connectedComponentIn_subset _ _).trans hcov)
      (by rw [hCR.inter_eq, inter_empty]) with hleft | hright
    · exact hleft
    · exact (disjoint_left.mp hCR (hp i)
        (hright (mem_connectedComponentIn (hsub i (hp i))))).elim
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : C i = C j := (hf i).symm.trans
      ((congrArg (fun c => (connectedComponentComplex K c).space) hij).trans (hf j))
    exact disjoint_left.mp (hdis hne) (hp i) (heq.subset (hp i))
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨x, hx⟩ := (isConnected_connectedComponentComplex_space K c).nonempty
    have hxK : x ∈ K.space := (iUnion_connectedComponentComplex_space K).subset
      (mem_iUnion.mpr ⟨c, hx⟩)
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.subset hxK)
    refine ⟨i, ?_⟩
    by_contra hne
    exact disjoint_left.mp (pairwise_disjoint_connectedComponentComplex_space K hne)
      ((hf i).symm.subset hxi) hx
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
