/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionBoundarySurface
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.exists_boundary_surface
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) :
    ∃ L : Geometry.SimplicialComplex ℝ E3, L.faces.Finite ∧ IsCombinatorialManifold 2 L ∧
      L.space = frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hV : ∀ w, IsPLBall 3 (section34CompactVertexBallImage src f₁ w) :=
    fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hpair : ∀ a b : Section34CompactVertexIndex K K', a ≠ b →
      (section34CompactVertexBallImage src f₁ a ∩
        section34CompactVertexBallImage src f₁ b).Nonempty →
      ∃ e : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage src f₁ e =
          section34CompactVertexBallImage src f₁ a ∩ section34CompactVertexBallImage src f₁ b ∧
        (e.1 : Set E3) = (a.1 : Set E3) ∪ (b.1 : Set E3) := by
    intro a b hab ⟨x, hxa, hxb⟩
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hab hxa hxb
    obtain ⟨u, v, -, heuv, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    have ha := eq_or_eq_of_section34CompactVertexIndex_subset e heuv
      (hcut.subset_of_mem_splitDiskImage hf₁ hxe hxa)
    have hb := eq_or_eq_of_section34CompactVertexIndex_subset e heuv
      (hcut.subset_of_mem_splitDiskImage hf₁ hxe hxb)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact ⟨e, heq, heuv⟩
    · exact ⟨e, heq.trans (inter_comm _ _), heuv.trans (union_comm _ _)⟩
    · exact (hab rfl).elim
  apply exists_combinatorial_surface_frontier_iUnion hV
  · intro a b hab hmeet
    obtain ⟨e, heq, -⟩ := hpair a b hab hmeet
    obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
    have hD : IsPLBall 2 (section34CompactVertexBallImage src f₁ a ∩
        section34CompactVertexBallImage src f₁ b) := ⟨q, heq ▸ hq⟩
    exact ⟨hD, (hV b).inter_subset_frontier_of_isPLBall hD (by decide)⟩
  · intro a b c hab hca hcb
    apply Set.disjoint_left.mpr
    intro x hxab hxc
    obtain ⟨e, heq, heab⟩ := hpair a b hab ⟨x, hxab⟩
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab
        (hcut.subset_of_mem_splitDiskImage hf₁ (heq.symm.subset hxab) hxc) with hc | hc
    · exact hca hc
    · exact hcb hc

theorem Section34CompactCutFrame.inter_closure_sdiff_disk_on_frontier
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {D : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDN : D ⊆ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) :
    D ∩ closure (frontier (⋃ w, section34CompactVertexBallImage src f₁ w) \ D) =
      q '' stdSimplexBoundary 2 := by
  obtain ⟨L, hLfin, hL, hLN⟩ := hcut.exists_boundary_surface hf₁
  have : Finite L.faces := hLfin.to_subtype
  rw [← hLN] at hDN ⊢
  exact hL.inter_closure_sdiff_disk L hq hDN

end DifferentialGeometry.Topology.PiecewiseLinear
