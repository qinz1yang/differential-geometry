/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkPropagation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactCutFrame.splitDiskImage_subset_vertexBallBoundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
    (hwe : w.1 ⊆ e.1) :
    section34CompactSplitDiskImage src f₁ e ⊆ section34CompactVertexBallImage srcBd f₁ w := by
  obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hD : IsPLBall 2 (section34CompactVertexBallImage src f₁ a ∩
      section34CompactVertexBallImage src f₁ b) := ⟨q, heq ▸ hq⟩
  rw [(hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier, heq]
  rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab hwe with rfl | rfl
  · exact (hcut.isPLCellOn_vertexBallImage hf₁ b).isPLBall_three
      |>.inter_subset_frontier_of_isPLBall hD (by decide)
  · rw [inter_comm]
    exact (hcut.isPLCellOn_vertexBallImage hf₁ a).isPLBall_three
      |>.inter_subset_frontier_of_isPLBall (inter_comm _ _ ▸ hD) (by decide)

theorem exists_vertex_disk_avoiding_all_split_disks
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ∃ (D : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = J ∧
        D ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
        ∀ e : Section34CompactEdgeIndex K K',
          Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  classical
  have hf₁ := hgraph.2.1
  have hcell := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hS : IsPLSphere 2 (section34CompactVertexBallImage srcBd f₁ w) := by
    rw [hcell.boundary_eq_frontier]
    exact hcell.isPLBall_three.isPLSphere_frontier
  have hJS : J ⊆ section34CompactVertexBallImage srcBd f₁ w := by
    rw [hcell.boundary_eq_frontier]
    intro x hx
    exact ⟨subset_closure (hJV hx), fun hi =>
      (hJN hx).2 (interior_mono (subset_iUnion _ w) hi)⟩
  have hJE : ∀ e : Section34CompactEdgeIndex K K',
      Disjoint J (section34CompactSplitDiskImage src f₁ e) :=
    hinv.disjoint_splitDiskImage_of_circle_subset_vertexBall hcut hf₁ s w hJ hJP hJV hJN
  have hws : Section34Incident w.1 s.1 := by
    by_contra hnot
    obtain ⟨x, hx⟩ := hJ.nonempty
    exact Set.notMem_empty x (hinv.2.2.1 s w hnot ▸ ⟨(hinv.1 s).boundary_subset (hJP hx), hJV hx⟩)
  choose p hp using fun e : Section34CompactEdgeIndex K K' =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
  let S := section34CompactVertexBallImage srcBd f₁ w \ J
  let c := fun e : Section34CompactEdgeIndex K K' => connectedComponentIn S (p e)
  have hDE : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      section34CompactSplitDiskImage src f₁ e ⊆ S := by
    intro e hwe x hx
    exact ⟨hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e hwe hx,
      fun hxJ => Set.disjoint_left.mp (hJE e) hxJ hx⟩
  have hface : ∀ t : Section34CompactSimplexIndex K 3, t ≠ s →
      ∀ e d : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d := by
    intro t hts e d hwe hwd het hdt
    have hwt : Section34Incident w.1 t.1 := (Finset.coe_subset.mpr hwe).trans het
    obtain ⟨D, q, hq, hqJ, hDS, hDdis⟩ :=
      exists_vertex_disk_avoiding_other_face_split_disks hinv hcut hgraph hts.symm
        w hwt hJ hJP hJV hJN
    have hconn := hS.isConnected_sdiff_of_isPLBall_two (show IsPLBall 2 D from ⟨q, hq⟩) hDS
    have hJW : J ⊆ D := by
      rw [← hqJ, ← hq.image_eq]
      exact image_mono fun x hx => hx.1
    have hsub : section34CompactVertexBallImage srcBd f₁ w \ D ⊆ S :=
      fun x hx => ⟨hx.1, fun hxJ => hx.2 (hJW hxJ)⟩
    have hpe : p e ∈ section34CompactVertexBallImage srcBd f₁ w \ D :=
      ⟨(hDE e hwe (hp e)).1, fun hxD => Set.disjoint_left.mp (hDdis e het) hxD (hp e)⟩
    have hpd : p d ∈ section34CompactVertexBallImage srcBd f₁ w \ D :=
      ⟨(hDE d hwd (hp d)).1, fun hxD => Set.disjoint_left.mp (hDdis d hdt) hxD (hp d)⟩
    exact (connectedComponentIn_eq
      (hconn.isPreconnected.subset_connectedComponentIn hpe hsub hpd))
  have hconstant := hcut.eq_on_incident_edges_of_eq_on_other_faces s w hws c hface
  obtain ⟨e₀, _, -, -, -, hwe₀, -⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident hcut.2.2.2.2.1 hcut.2.2.1 s w hws
  let Y := c e₀
  have hYS : Y ⊆ S := connectedComponentIn_subset _ _
  have hEY : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      section34CompactSplitDiskImage src f₁ e ⊆ Y := by
    intro e hwe x hx
    obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
    have hD : IsPLBall 2 (section34CompactSplitDiskImage src f₁ e) := ⟨q, hq⟩
    have hmem := hD.isConnected.isPreconnected.subset_connectedComponentIn (hp e) (hDE e hwe) hx
    change x ∈ c e at hmem
    change x ∈ c e₀
    rwa [hconstant e e₀ hwe hwe₀] at hmem
  have hYJ : Disjoint Y J := Set.disjoint_left.mpr fun x hx hxJ => (hYS hx).2 hxJ
  obtain ⟨D, q, hq, hDS, hYD, hqJ⟩ :=
    hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected isPreconnected_connectedComponentIn
      (hYS.trans sdiff_subset) hJ hJS hYJ
  refine ⟨D, q, hq, hqJ, hDS, fun e => ?_⟩
  by_cases hwe : w.1 ⊆ e.1
  · exact (hYD.mono_left (hEY e hwe)).symm
  · refine Set.disjoint_left.mpr fun x hxD hxE => hwe ?_
    exact hcut.subset_of_mem_splitDiskImage hf₁ hxE (hcell.boundary_subset (hDS hxD))

end DifferentialGeometry.Topology.PiecewiseLinear
