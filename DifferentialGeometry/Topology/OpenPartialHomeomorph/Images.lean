import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isImage_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) : e.IsImage s (e '' s) := by
  apply IsImage.of_image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr hs, inter_eq_right.mpr ht]

theorem image_interior_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) : e '' interior s = interior (e '' s) := by
  have h := (e.isImage_image_of_subset_source hs).interior.image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr (interior_subset.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h

theorem image_frontier_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) (hsc : IsClosed s) (htc : IsClosed (e '' s)) :
    e '' frontier s = frontier (e '' s) := by
  have h := (e.isImage_image_of_subset_source hs).frontier.image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr (hsc.frontier_subset.trans hs),
    inter_eq_right.mpr (htc.frontier_subset.trans ht)] at h
  exact h

theorem closure_interior_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) (hreg : closure (interior s) = s)
    (hclosed : IsClosed (e '' s)) : closure (interior (e '' s)) = e '' s := by
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  rw [← e.image_interior_of_subset_source hs]
  have hc : ContinuousOn e (closure (interior s)) := by
    rw [hreg]
    exact e.continuousOn.mono hs
  simpa only [hreg] using hc.image_closure

end OpenPartialHomeomorph
