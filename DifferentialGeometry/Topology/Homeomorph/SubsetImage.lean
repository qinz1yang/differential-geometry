/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

/-! Images of subsets and compact frontiers under open partial homeomorphisms. -/

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isImage_image_of_subset_source (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hs : s ⊆ e.source) : e.IsImage s (e '' s) := by
  intro x hx
  refine ⟨?_, fun h => mem_image_of_mem e h⟩
  rintro ⟨y, hy, heq⟩
  exact e.injOn (hs hy) hx heq ▸ hy

theorem image_interior_of_subset_source (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hs : s ⊆ e.source) : e '' interior s = interior (e '' s) := by
  have ht : e '' s ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have h := (e.isImage_image_of_subset_source hs).interior.image_eq
  rwa [inter_eq_right.mpr (interior_subset.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h

theorem image_frontier_of_isCompact [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} (hc : IsCompact s)
    (hs : s ⊆ e.source) : e '' frontier s = frontier (e '' s) := by
  have ht : e '' s ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hclosed : IsClosed (e '' s) :=
    (hc.image_of_continuousOn (e.continuousOn.mono hs)).isClosed
  have h := (e.isImage_image_of_subset_source hs).frontier.image_eq
  rwa [inter_eq_right.mpr (hc.isClosed.frontier_subset.trans hs),
    inter_eq_right.mpr (hclosed.frontier_subset.trans ht)] at h

end OpenPartialHomeomorph
