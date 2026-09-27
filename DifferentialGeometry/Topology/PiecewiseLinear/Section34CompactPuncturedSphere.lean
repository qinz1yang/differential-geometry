/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMouthAvoidance
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPolygonFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPuncturedLink

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem Section34CompactFaceBallInvariants.disjoint_splitDiskImage_of_not_incident
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K')
    (he : ¬ Section34Incident e.1 s.1) :
    Disjoint (fbl s) (section34CompactSplitDiskImage src f₁ e) := by
  apply Set.disjoint_left.mpr
  intro x hxP hxE
  obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hinc : ∀ w : Section34CompactVertexIndex K K',
      x ∈ section34CompactVertexBallImage src f₁ w → Section34Incident w.1 s.1 := by
    intro w hxw
    by_contra hnot
    exact Set.notMem_empty x (hinv.2.2.1 s w hnot ▸ ⟨hxP, hxw⟩)
  apply he
  change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
  rw [heab]
  exact union_subset (hinc a (heq.subset hxE).1) (hinc b (heq.subset hxE).2)

theorem Section34CompactCutFrame.splitDiskBoundary_subset_frontier_vertexBallImages
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) (e : Section34CompactEdgeIndex K K') :
    section34CompactSplitDiskImage srcBd f₁ e ⊆
      frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hV : ∀ w, IsPLBall 3 (section34CompactVertexBallImage src f₁ w) :=
    fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  obtain ⟨q, hq, -⟩ := hcell.exists_isPLHomeomorphOn_stdSimplex
  have hD : IsPLBall 2 (section34CompactVertexBallImage src f₁ a ∩
      section34CompactVertexBallImage src f₁ b) := ⟨q, heq ▸ hq⟩
  have hDa : section34CompactSplitDiskImage src f₁ e ⊆
      frontier (section34CompactVertexBallImage src f₁ a) := by
    rw [heq]
    exact (hV b).inter_subset_frontier_of_isPLBall hD (by decide)
  have hfr := boundary_subset_frontier_union_of_inter_eq (hV a) (hV b) hcell heq.symm hDa
  intro x hx
  have hxE := hcell.boundary_subset hx
  have hloc := eventually_mem_frontier_iUnion_iff_pair (fun w => (hV w).isPolyhedron.isClosed)
    (i := a) (j := b) (x := x) (by
      intro w hwa hwb hxw
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab
        (hcut.subset_of_mem_splitDiskImage hf₁ hxE hxw) with hw | hw
      · exact hwa hw
      · exact hwb hw)
  exact hloc.self_of_nhds.mpr (hfr hx)

theorem exists_connected_set_containing_other_split_disks
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (e₀ : Section34CompactEdgeIndex K K') (hwe₀ : w.1 ⊆ e₀.1)
    (he₀s : Section34Incident e₀.1 s.1) {J : Set E3} (hJ : IsPLSphere 1 J)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v))
    (hJP : J ⊆ fblBd s ∪ section34CompactSplitDiskImage srcBd f₁ e₀)
    (hJE : ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
      Disjoint J (section34CompactSplitDiskImage src f₁ e)) :
    ∃ Y : Set E3, IsConnected Y ∧ Y ⊆ section34CompactVertexBallImage srcBd f₁ w \ J ∧
      ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → e ≠ e₀ →
        section34CompactSplitDiskImage src f₁ e ⊆ Y := by
  classical
  have hf₁ := hgraph.2.1
  have hcell := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hS : IsPLSphere 2 (section34CompactVertexBallImage srcBd f₁ w) := by
    rw [hcell.boundary_eq_frontier]
    exact hcell.isPLBall_three.isPLSphere_frontier
  have hJt : ∀ t : Section34CompactSimplexIndex K 3, ¬ Section34Incident e₀.1 t.1 →
      Disjoint J (fblBd t) := by
    intro t ht
    have hst : s ≠ t := fun h => ht (h ▸ he₀s)
    apply Set.disjoint_left.mpr
    intro x hxJ hxt
    rcases hJP hxJ with hxs | hxe
    · exact (hJN hxJ).2 (hinv.2.2.2.1 s t hst
        ⟨(hinv.1 s).boundary_subset hxs, (hinv.1 t).boundary_subset hxt⟩)
    · exact Set.disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ t e₀ ht)
        ((hinv.1 t).boundary_subset hxt)
        ((hcut.isPLCellOn_splitDiskImage hf₁ e₀).boundary_subset hxe)
  choose p hp using fun e : Section34CompactEdgeIndex K K' =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
  let S := section34CompactVertexBallImage srcBd f₁ w \ J
  let c := fun e : Section34CompactEdgeIndex K K' => connectedComponentIn S (p e)
  have hDE : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → e ≠ e₀ →
      section34CompactSplitDiskImage src f₁ e ⊆ S := by
    intro e hwe he x hx
    exact ⟨hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e hwe hx,
      fun hxJ => Set.disjoint_left.mp (hJE e he) hxJ hx⟩
  have hface : ∀ t : Section34CompactSimplexIndex K 3, ¬ Section34Incident e₀.1 t.1 →
      ∀ e d : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d := by
    intro t ht e d hwe hwd het hdt
    have he₀ : e ≠ e₀ := fun h => ht (h ▸ het)
    have hd₀ : d ≠ e₀ := fun h => ht (h ▸ hdt)
    have hwt : Section34Incident w.1 t.1 := (Finset.coe_subset.mpr hwe).trans het
    obtain ⟨D, q, hq, hqJ, hDS, hDdis⟩ := exists_vertex_disk_of_disjoint_face_trace
      hinv hcut hgraph t w hwt hJ hJV hJN (hJt t ht) (by
        intro a hat
        exact (hJE a (fun h => ht (h ▸ hat))).mono_right
          (hcut.isPLCellOn_splitDiskImage hf₁ a).boundary_subset)
    have hconn := hS.isConnected_sdiff_of_isPLBall_two (show IsPLBall 2 D from ⟨q, hq⟩) hDS
    have hJD : J ⊆ D := by
      rw [← hqJ, ← hq.image_eq]
      exact image_mono fun x hx => hx.1
    have hsub : section34CompactVertexBallImage srcBd f₁ w \ D ⊆ S :=
      fun x hx => ⟨hx.1, fun hxJ => hx.2 (hJD hxJ)⟩
    have hpe : p e ∈ section34CompactVertexBallImage srcBd f₁ w \ D :=
      ⟨(hDE e hwe he₀ (hp e)).1, fun hxD => Set.disjoint_left.mp (hDdis e het) hxD (hp e)⟩
    have hpd : p d ∈ section34CompactVertexBallImage srcBd f₁ w \ D :=
      ⟨(hDE d hwd hd₀ (hp d)).1, fun hxD => Set.disjoint_left.mp (hDdis d hdt) hxD (hp d)⟩
    exact connectedComponentIn_eq (hconn.isPreconnected.subset_connectedComponentIn hpe hsub hpd)
  have hconstant := hcut.eq_on_other_edges_of_eq_on_faces_avoiding_edge w e₀ hwe₀ c hface
  have hws : Section34Incident w.1 s.1 := (Finset.coe_subset.mpr hwe₀).trans he₀s
  obtain ⟨e₁, e₂, h₁₂, -, -, hw₁, hw₂, -⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident hcut.2.2.2.2.1 hcut.2.2.1 s w hws
  obtain ⟨b, hwb, hb₀⟩ : ∃ b : Section34CompactEdgeIndex K K', w.1 ⊆ b.1 ∧ b ≠ e₀ := by
    by_cases h₁₀ : e₁ = e₀
    · exact ⟨e₂, hw₂, fun h₂₀ => h₁₂ (h₁₀.trans h₂₀.symm)⟩
    · exact ⟨e₁, hw₁, h₁₀⟩
  let Y := c b
  have hYS : Y ⊆ S := connectedComponentIn_subset _ _
  refine ⟨Y, ⟨⟨p b, mem_connectedComponentIn (hDE b hwb hb₀ (hp b))⟩,
    isPreconnected_connectedComponentIn⟩, hYS, fun e hwe he₀ x hx => ?_⟩
  obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hD : IsPLBall 2 (section34CompactSplitDiskImage src f₁ e) := ⟨q, hq⟩
  have hmem := hD.isConnected.isPreconnected.subset_connectedComponentIn (hp e) (hDE e hwe he₀) hx
  change x ∈ c e at hmem
  change x ∈ c b
  rwa [hconstant e b hwe hwb he₀ hb₀] at hmem

end DifferentialGeometry.Topology.PiecewiseLinear
