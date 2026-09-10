import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace DifferentialGeometry.Topology.Embedding

open Set

theorem image_interior_of_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) (A : Set X) :
    f '' interior A = interior (f '' A) := by
  have hpre : f ⁻¹' interior (f '' A) = interior A := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      preimage_image_eq _ hf.injective]
  rw [← hpre]
  exact image_preimage_eq_of_subset (interior_subset.trans (image_subset_range _ _))

theorem image_frontier_of_isOpenEmbedding_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) {A : Set X}
    (hA : IsCompact A) : f '' frontier A = frontier (f '' A) := by
  have hpre : f ⁻¹' frontier (f '' A) = frontier A := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      preimage_image_eq _ hf.injective]
  rw [← hpre]
  exact image_preimage_eq_of_subset
    ((hA.image hf.continuous).isClosed.frontier_subset.trans (image_subset_range _ _))

end DifferentialGeometry.Topology.Embedding
