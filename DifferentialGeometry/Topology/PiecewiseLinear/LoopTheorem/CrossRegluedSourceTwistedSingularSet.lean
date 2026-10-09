/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedPiece
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductNormal

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem twistedStripMap_core_mem_frontier_iff {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    twistedStripMap (0, t) ∈ frontier twistedStripSide ↔ t = 0 ∨ t = 1 := by
  have hp : (0, t) ∈ twistedSourceRect := ⟨⟨by norm_num, by norm_num⟩, ht⟩
  rw [twistedStripMap_mem_frontier_side_iff hp, frontier_twistedSourceRect]
  simp only [mem_sdiff, and_iff_right hp, mem_prod, mem_Ioo]
  norm_num only at *
  simp only [true_and]
  constructor
  · intro h
    by_cases h0 : t = 0
    · exact Or.inl h0
    · exact Or.inr (by
        have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
        by_contra h1
        exact h ⟨ht0, lt_of_le_of_ne ht.2 h1⟩)
  · rintro (rfl | rfl) <;> simp

theorem twistedStripCell_doublePointSet_inter_frontier :
    doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∩ frontier twistedStripSide =
      {twistedStripMap (0, 0), twistedStripMap (0, 1)} := by
  rw [twistedStripCell_doublePointSet]
  apply Subset.antisymm
  · rintro y ⟨⟨t, ht, rfl⟩, hy⟩
    rcases (twistedStripMap_core_mem_frontier_iff ht).mp hy with rfl | rfl <;> simp
  · rintro y (rfl | rfl)
    · exact ⟨mem_image_of_mem _ (by norm_num),
        (twistedStripMap_core_mem_frontier_iff (by norm_num)).mpr (Or.inl rfl)⟩
    · exact ⟨mem_image_of_mem _ (by norm_num),
        (twistedStripMap_core_mem_frontier_iff (by norm_num)).mpr (Or.inr rfl)⟩

open Classical in
theorem twistedStripCell_exists_singular_complex :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 K ∧
        K.space ⊆ halfTurnSlab 0 ∧
        halfTurnEuclideanProjection '' K.space =
          doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∧
        halfTurnEuclideanProjection '' (boundaryComplex 1 K).space =
          doublePointSet (⇑twistedStripCell) twistedStripCell.domain ∩
            frontier twistedStripSide := by
  classical
  obtain ⟨K, hfin, hman, hspace, hboundary⟩ :=
    exists_simplicialComplex_vertical_interval (-1 / 2)
  refine ⟨K, hfin, hman, ?_, ?_, ?_⟩
  · rw [hspace]
    rintro _ ⟨⟨⟨x, y⟩, t⟩, ⟨hxy, ht⟩, rfl⟩
    change (x, y) = (0, -1 / 2) at hxy
    cases hxy
    change (spliceEmbedding.symm (spliceEmbedding ((0, -1 / 2), t))).1.1 ∈
      Ioo (0 - 1 / 4) (0 + 1 / 4)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    norm_num
  · rw [hspace, twistedStripCell_doublePointSet, ← image_comp]
    apply Subset.antisymm
    · rintro _ ⟨⟨⟨x, y⟩, t⟩, ⟨hxy, ht⟩, rfl⟩
      change (x, y) = (0, -1 / 2) at hxy
      cases hxy
      refine ⟨t, ht, ?_⟩
      norm_num [halfTurnEuclideanProjection, twistedStripMap]
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨((0, -1 / 2), t), ⟨rfl, ht⟩, ?_⟩
      norm_num [halfTurnEuclideanProjection, twistedStripMap]
  · rw [hboundary, image_pair, twistedStripCell_doublePointSet_inter_frontier]
    norm_num [halfTurnEuclideanProjection, twistedStripMap]

theorem twistedStripCell_nonempty_normalSingularSetTriangulation :
    Nonempty (NormalSingularSetTriangulation twistedStripCell
      (frontier twistedStripSide)) := by
  classical
  obtain ⟨K, hfin, hman, hslab, hspace, hboundary⟩ :=
    twistedStripCell_exists_singular_complex
  let T := halfTurnSlabPiece 0 K hfin hslab
  exact ⟨{
    carrier := halfTurnEuclideanProjection '' K.space
    piece := ⟨3, T⟩
    complex := K
    finite_faces := hfin
    faces_subset := subset_rfl
    isManifoldWithBoundary := hman
    map_space := hspace
    map_boundary := hboundary }⟩

end DifferentialGeometry.Topology.PiecewiseLinear
