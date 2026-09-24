/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Separation.Hausdorff

/-! Images of subsets and compact frontiers under open partial homeomorphisms. -/

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem image_frontier_of_isCompact [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} (hc : IsCompact s)
    (hs : s ⊆ e.source) : e '' frontier s = frontier (e '' s) :=
  e.image_frontier_of_subset_source hs hc.isClosed
    (hc.image_of_continuousOn (e.continuousOn.mono hs)).isClosed

end OpenPartialHomeomorph
