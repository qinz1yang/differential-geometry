import DifferentialGeometry.Topology.Connected.FrontierCover
import DifferentialGeometry.Topology.Embedding.Frontier

open Set Filter Topology

namespace DifferentialGeometry.Topology

theorem cover_and_endpoint_subset_of_embedded_collar
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : _root_.Topology.IsClosedEmbedding f)
    (hregular : closure (interior (range f)) = range f)
    (hconnected : IsPreconnected (interior (range f)))
    (P K Q : Set X) (D : Set Y)
    (hP : IsClosed P) (hK : IsClosed K) (hQ : IsClosed Q)
    (hcover : P ∪ K ∪ Q = univ) (hdisj : Disjoint P Q)
    (hD : IsClosed D) (hKD : f '' K ⊆ D)
    (hinternal : f '' K ⊆ interior (range f))
    (hfront : frontier D ⊆ frontier (range f) ∪ f '' (K ∩ Q))
    (hne : (K ∩ Q).Nonempty) :
    range f ⊆ D ∪ f '' Q ∧ (interior Q)ᶜ ⊆ f ⁻¹' D := by
  have hfrontQ : frontier Q ⊆ K ∩ Q := by
    intro x hx
    have hxQ : x ∈ Q := hQ.frontier_subset hx
    refine ⟨?_, hxQ⟩
    by_contra hxK
    have hxP : x ∉ P := fun h ↦ Set.disjoint_left.mp hdisj h hxQ
    have hsub : (P ∪ K)ᶜ ⊆ Q := by
      intro y hy
      exact (show y ∈ P ∪ K ∪ Q from hcover.symm ▸ mem_univ y).resolve_left hy
    exact hx.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((hP.union hK).isOpen_compl.mem_nhds
        (not_or.mpr ⟨hxP, hxK⟩)) hsub))
  have hclosedP : IsClosed (f '' P) := hf.isClosedMap P hP
  have hclosedQ : IsClosed (f '' Q) := hf.isClosedMap Q hQ
  have hseam : f '' (K ∩ Q) ⊆ interior (D ∪ f '' Q) := by
    rintro y ⟨x, hx, rfl⟩
    have hxP : f x ∉ f '' P := by
      rintro ⟨z, hz, hzx⟩
      exact Set.disjoint_left.mp hdisj (hf.injective hzx ▸ hz) hx.2
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset
      ((isOpen_interior.inter hclosedP.isOpen_compl).mem_nhds
        ⟨hinternal ⟨x, hx.1, rfl⟩, hxP⟩)
    rintro z ⟨hzrange, hzP⟩
    obtain ⟨w, rfl⟩ := interior_subset hzrange
    rcases (show w ∈ P ∪ K ∪ Q from hcover.symm ▸ mem_univ w) with (hp | hk) | hq
    · exact False.elim (hzP ⟨w, hp, rfl⟩)
    · exact Or.inl (hKD ⟨w, hk, rfl⟩)
    · exact Or.inr ⟨w, hq, rfl⟩
  have hfrontUnion : frontier (D ∪ f '' Q) ⊆ frontier (range f) := by
    intro y hy
    have hcases : y ∈ frontier (range f) ∪ f '' (K ∩ Q) := by
      rcases frontier_union_subset D (f '' Q) hy with hd | hq
      · exact hfront hd.1
      · rcases Embedding.frontier_image_subset_of_isEmbedding hf.isEmbedding Q hq.2 with hr | hq'
        · exact Or.inl hr
        · exact Or.inr (image_mono hfrontQ hq')
    exact hcases.resolve_right (fun hs ↦ hy.2 (hseam hs))
  have hmeet : (interior (range f) ∩ interior (D ∪ f '' Q)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨f x, hinternal ⟨x, hx.1, rfl⟩, hseam ⟨x, hx, rfl⟩⟩
  have hcovered : range f ⊆ D ∪ f '' Q :=
    subset_of_frontier_subset_of_closure_interior_eq
      (hD.union hclosedQ) hregular hconnected hfrontUnion hmeet
  refine ⟨hcovered, ?_⟩
  intro x hx
  rcases hcovered ⟨x, rfl⟩ with hd | hq
  · exact hd
  · have hxQ : x ∈ Q := hf.injective.mem_set_image.mp hq
    exact hKD ⟨x, (hfrontQ ⟨subset_closure hxQ, hx⟩).1, rfl⟩

end DifferentialGeometry.Topology
