/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compact_cut_primary_cover {K : Geometry.SimplicialComplex ℝ E3}
    (hcoface : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) (N : Set E3) :
    N ∪ (⋃ t : Section34CompactSimplexIndex K 4,
      closure (convexHull ℝ (t.1 : Set E3) \ N)) = K.space ∪ N := by
  classical
  apply Subset.antisymm
  · refine union_subset subset_union_right (iUnion_subset fun t => ?_)
    exact (closure_minimal sdiff_subset
      (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
        ((K.convexHull_subset_space t.2.1).trans subset_union_left)
  · rintro x (hxK | hxN)
    · by_cases hxN : x ∈ N
      · exact Or.inl hxN
      · obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
        obtain ⟨t, ht, hst, hcard⟩ := hcoface s hs
        exact Or.inr (mem_iUnion.mpr ⟨⟨t, ht, hcard⟩, subset_closure
          ⟨convexHull_mono (Finset.coe_subset.mpr hst) hxs, hxN⟩⟩)
    · exact Or.inl hxN

theorem IsCombinatorialManifoldWithBoundary.compact_dual_cut_cover
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let N := ⋃ v ∈ K.vertices, (graphDualCell M L v).space
    N ∪ (⋃ t : Section34CompactSimplexIndex K 4,
      closure (convexHull ℝ (t.1 : Set E3) \ N)) = K.space ∪ N := by
  dsimp only
  exact compact_cut_primary_cover (fun _ hs => hK.exists_face_superset_card_eq hs) _

end DifferentialGeometry.Topology.PiecewiseLinear
