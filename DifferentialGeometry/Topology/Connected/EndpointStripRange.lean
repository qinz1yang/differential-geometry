import DifferentialGeometry.Topology.Connected.FrontierCover
import DifferentialGeometry.Topology.Embedding.Frontier

open Set Filter Topology

namespace DifferentialGeometry.Topology

theorem endpoint_strip_subset_image_of_embedded_collar
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (P K Q : Set X) (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (Sminus Splus : Set X)
    (hboundary : frontier (range f) ⊆ f '' Sminus ∪ f '' Splus)
    (hplusQ : Splus ⊆ Q) (hplusBoundary : f '' Splus ⊆ frontier (range f))
    (hinternal : f '' K ⊆ interior (range f))
    (D : Set Y) (hregular : closure (interior D) = D)
    (hconnected : IsPreconnected (interior D)) (hKD : f '' K ⊆ D)
    (hne : (interior (f '' K)).Nonempty)
    (hsections : f '' Sminus ∪ f '' (K ∩ Q) ⊆ frontier D) :
    D ⊆ f '' (P ∪ K) := by
  have hclosed : IsClosed (f '' (P ∪ K)) := hf.isClosedMap _ (hP.union hK)
  have hfrontRelative : frontier (P ∪ K) ⊆ K ∩ Q := by
    intro x hx
    have hxPK : x ∈ P ∪ K := (hP.union hK).frontier_subset hx
    have hxQ : x ∈ Q := by
      by_contra hxQ
      have hsub : Qᶜ ⊆ P ∪ K := by
        intro y hy
        exact (show y ∈ P ∪ K ∪ Q from hcover.symm ▸ mem_univ y).resolve_right hy
      exact hx.2 (mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hQ.isOpen_compl.mem_nhds hxQ) hsub))
    exact ⟨hxPK.resolve_left (fun hp ↦ Set.disjoint_left.mp hdisj hp hxQ), hxQ⟩
  have hfrontImage : frontier (f '' (P ∪ K)) ⊆ f '' Sminus ∪ f '' (K ∩ Q) := by
    intro y hy
    rcases Embedding.frontier_image_subset_of_isEmbedding hf.isEmbedding (P ∪ K) hy with
      hr | hrel
    · rcases hboundary hr with hm | hp
      · exact Or.inl hm
      · obtain ⟨x, hx, rfl⟩ := hclosed.frontier_subset hy
        have hxplus : x ∈ Splus := hf.injective.mem_set_image.mp hp
        rcases hx with hxP | hxK
        · exact False.elim (Set.disjoint_left.mp hdisj hxP (hplusQ hxplus))
        · exact False.elim ((hplusBoundary hp).2 (hinternal ⟨x, hxK, rfl⟩))
    · exact Or.inr (image_mono hfrontRelative hrel)
  have hmeet : (interior D ∩ interior (f '' (P ∪ K))).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, interior_mono hKD hy,
      interior_mono (image_mono (show K ⊆ P ∪ K from subset_union_right)) hy⟩
  exact subset_of_frontier_subset_of_closure_interior_eq hclosed hregular hconnected
    (hfrontImage.trans hsections) hmeet

end DifferentialGeometry.Topology
