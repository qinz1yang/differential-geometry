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

end OpenPartialHomeomorph
