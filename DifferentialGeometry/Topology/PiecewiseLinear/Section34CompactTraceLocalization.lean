/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.exists_vertex_ball_of_connected_avoiding_split_disks
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) {A : Set E3} (hA : IsConnected A)
    (hAN : A ⊆ ⋃ v, section34CompactVertexBallImage src f₁ v)
    (hAE : ∀ e : Section34CompactEdgeIndex K K',
      Disjoint A (section34CompactSplitDiskImage src f₁ e)) :
    ∃ w : Section34CompactVertexIndex K K', A ⊆ section34CompactVertexBallImage src f₁ w := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hV : ∀ w, IsClosed (section34CompactVertexBallImage src f₁ w) :=
    fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed
  obtain ⟨p, hp⟩ := hA.nonempty
  obtain ⟨w, hpw⟩ := mem_iUnion.mp (hAN hp)
  let U := ⋃ v ∈ {v : Section34CompactVertexIndex K K' | v ≠ w},
    section34CompactVertexBallImage src f₁ v
  have hU : IsClosed U := (Set.toFinite _).isClosed_biUnion fun v _ => hV v
  have hcover : A ⊆ section34CompactVertexBallImage src f₁ w ∪ U := by
    intro x hx
    obtain ⟨v, hxv⟩ := mem_iUnion.mp (hAN hx)
    by_cases hvw : v = w
    · exact Or.inl (hvw ▸ hxv)
    · exact Or.inr (mem_iUnion₂.mpr ⟨v, hvw, hxv⟩)
  have hdis : A ∩ (section34CompactVertexBallImage src f₁ w ∩ U) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxA, hxw, hxU⟩
    obtain ⟨v, hvw, hxv⟩ := mem_iUnion₂.mp hxU
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hvw hxv hxw
    exact Set.disjoint_left.mp (hAE e) hxA hxe
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA.isPreconnected
      (section34CompactVertexBallImage src f₁ w) U (hV w) hU hcover hdis with hw | hU'
  · exact ⟨w, hw⟩
  · exact (Set.notMem_empty p (hdis ▸ ⟨hp, hpw, hU' hp⟩)).elim

theorem Section34CompactCutFrame.exists_vertex_boundary_of_arc_avoiding_split_disks
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) {B : Set E3} {η : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B)
    (hBN : B ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
    (hBE : ∀ e : Section34CompactEdgeIndex K K',
      Disjoint (B \ {η 0, η 1}) (section34CompactSplitDiskImage src f₁ e)) :
    ∃ w : Section34CompactVertexIndex K K', B ⊆ section34CompactVertexBallImage srcBd f₁ w := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hN : IsClosed (⋃ v, section34CompactVertexBallImage src f₁ v) :=
    isClosed_iUnion_of_finite fun v => (hcut.isPLCellOn_vertexBallImage hf₁ v).isCompact.isClosed
  obtain ⟨w, hw⟩ := hcut.exists_vertex_ball_of_connected_avoiding_split_disks hf₁
    (hη.isConnected_sdiff_endpoints zero_lt_one)
    (sdiff_subset.trans (hBN.trans hN.frontier_subset)) hBE
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hBW : B ⊆ section34CompactVertexBallImage src f₁ w := by
    rw [← hη.closure_sdiff_endpoints zero_lt_one]
    exact closure_minimal hw hV.isCompact.isClosed
  refine ⟨w, ?_⟩
  rw [hV.boundary_eq_frontier]
  intro x hx
  exact ⟨subset_closure (hBW hx), fun hxi => (hBN hx).2
    (interior_mono (subset_iUnion _ w) hxi)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
