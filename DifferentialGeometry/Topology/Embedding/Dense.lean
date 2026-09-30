import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
open Set Filter Topology
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace X] [T2Space Y] {f : X → Y}

theorem IsDenseInducing.isOpen_range (hf : IsDenseInducing f) : IsOpen (range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, rfl⟩
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have h := hf.closure_image_mem_nhds hxK
  rw [(hK.image hf.continuous).isClosed.closure_eq] at h
  exact mem_of_superset h (image_subset_range _ _)

theorem IsDenseEmbedding.isOpenEmbedding (hf : IsDenseEmbedding f) : IsOpenEmbedding f :=
  ⟨hf.isEmbedding, hf.isDenseInducing.isOpen_range⟩
