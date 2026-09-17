import DifferentialGeometry.Topology.Embedding.CompactFrontier

open Set Filter Topology

namespace DifferentialGeometry.Topology.Embedding

theorem interior_image_of_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) (A : Set X) :
    interior (f '' A) = f '' interior A :=
  (image_interior_of_isOpenEmbedding hf A).symm

theorem frontier_image_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsEmbedding f) (A : Set X) :
    frontier (f '' A) = f '' frontier A ∪ (frontier (range f) ∩ closure (f '' A)) := by
  have hsub : f '' A ⊆ range f := by
    rintro y ⟨x, _, hxy⟩
    exact ⟨x, hxy⟩
  apply Subset.antisymm
  · intro y hy
    by_cases hr : y ∈ frontier (range f)
    · exact Or.inr ⟨hr, hy.1⟩
    · have hri : y ∈ interior (range f) := by
        by_contra h
        exact hr ⟨closure_mono hsub hy.1, h⟩
      obtain ⟨x, rfl⟩ := interior_subset hri
      have hxc : x ∈ closure A := by
        rw [hf.closure_eq_preimage_closure_image]
        exact hy.1
      refine Or.inl ⟨x, ⟨hxc, ?_⟩, rfl⟩
      intro hxi
      have hn : f '' A ∈ Filter.map f (𝓝 x) :=
        Filter.image_mem_map (mem_interior_iff_mem_nhds.mp hxi)
      rw [hf.map_nhds_of_mem x (mem_interior_iff_mem_nhds.mp hri)] at hn
      exact hy.2 (mem_interior_iff_mem_nhds.mpr hn)
  · rintro y (⟨x, hx, rfl⟩ | ⟨hr, hc⟩)
    · refine ⟨image_closure_subset_closure_image hf.continuous ⟨x, hx.1, rfl⟩, ?_⟩
      intro hi
      have hxi : x ∈ interior (f ⁻¹' (f '' A)) :=
        preimage_interior_subset_interior_preimage hf.continuous hi
      rw [hf.injective.preimage_image] at hxi
      exact hx.2 hxi
    · exact ⟨hc, fun hi ↦ hr.2 (interior_mono hsub hi)⟩

theorem frontier_image_subset_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsEmbedding f) (A : Set X) :
    frontier (f '' A) ⊆ frontier (range f) ∪ f '' frontier A := by
  rw [frontier_image_of_isEmbedding hf A]
  exact union_subset subset_union_right (inter_subset_left.trans subset_union_left)

end DifferentialGeometry.Topology.Embedding
