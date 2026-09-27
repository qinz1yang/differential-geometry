/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem exists_section34CompactBigonBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3)
    (hop : Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    ∃ (w v : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
      (B B' Bb Dj Jd : Set E3),
      IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
      Bb ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ e', section34CompactSplitDiskImage src f₁ e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
        frontier (⋃ z, section34CompactVertexBallImage src f₁ z) ∧ Jd = B ∪ B' ∧
      (∀ s', Disjoint (Dj \ Jd) (fblBd s')) ∧ w ≠ v ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (v.1 : Set E3) ∧
      Section34Incident w.1 s.1 ∧ Section34Incident v.1 s.1 ∧ Section34Incident e.1 s.1 ∧
      section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ w ∩ section34CompactVertexBallImage src f₁ v ∧
      IsPLBall 3 (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ v) ∧ IsPLBall 2 Dj ∧
      Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ v) ∧
      section34CompactSplitDiskImage srcBd f₁ e ⊆
        frontier (section34CompactVertexBallImage src f₁ w ∪
          section34CompactVertexBallImage src f₁ v) := by
  obtain ⟨-, hf₁, -, -, -, -, -, -, -, -, -⟩ := hgraph
  obtain ⟨hfcell, -, hfavoid, -, -, -, -, -, -, -, -⟩ := hinv
  obtain ⟨w, e, B, B', Bb, Dj, Jd, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean⟩ := hop
  obtain ⟨b, hb, hbb⟩ := hB.exists_isPLHomeomorphOn_stdSimplex
  have hBb : Bb.Nonempty := by
    rw [hbb]
    exact (nonempty_stdSimplexBoundary_of_pos (by decide : 0 < 1)).image b
  obtain ⟨x, hx⟩ := hBb
  have hxF := (hfcell s).boundary_subset (hBf (hB.boundary_subset hx))
  have hxw := (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset
    (hBw (hB.boundary_subset hx))
  have hxe := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset (hBbe hx)
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hxe hxw
  obtain ⟨a, d, had, head, hEad⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hp : ∃ v : Section34CompactVertexIndex K K', w ≠ v ∧
      (e.1 : Set E3) = (w.1 : Set E3) ∪ (v.1 : Set E3) ∧
      section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ w ∩ section34CompactVertexBallImage src f₁ v := by
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e head hwe with rfl | rfl
    · exact ⟨d, had, head, hEad⟩
    · exact ⟨a, had.symm, head.trans (union_comm _ _), hEad.trans (inter_comm _ _)⟩
  obtain ⟨v, hwv, hewv, hinter⟩ := hp
  have hinc : ∀ z : Section34CompactVertexIndex K K',
      x ∈ section34CompactVertexBallImage src f₁ z → Section34Incident z.1 s.1 := by
    intro z hxz
    by_contra hz
    exact notMem_empty x ((hfavoid s z hz) ▸ ⟨hxF, hxz⟩)
  have hwi := hinc w hxw
  have hvi := hinc v (hinter ▸ hxe).2
  have hei : Section34Incident e.1 s.1 := by
    change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [hewv]
    exact union_subset hwi hvi
  have hEbd : ∀ z : Section34CompactVertexIndex K K',
      section34CompactSplitDiskImage src f₁ e ⊆ section34CompactVertexBallImage src f₁ z →
      section34CompactSplitDiskImage src f₁ e ⊆
        frontier (section34CompactVertexBallImage src f₁ z) := by
    intro z hz
    have hsrc : src (.splitDisk e) ⊆ src (.vertexBall z) := by
      intro y hy
      obtain ⟨y', hy', heq⟩ := hz (mem_image_of_mem f₁ hy)
      exact hf₁.bijOn.injOn (subset_iUnion (fun a => src (.vertexBall a)) z hy')
        (hcut.splitDisk_subset_cutNeighborhood e hy) heq ▸ hy'
    rw [← (hcut.isPLCellOn_vertexBallImage hf₁ z).boundary_eq_frontier]
    refine image_mono fun y hy => ?_
    rw [hcut.2.2.2.2.2.2.2.1 (.vertexBall z)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsrc, by simp⟩, hy⟩
  have hEw := hEbd w (by rw [hinter]; exact inter_subset_left)
  have hEv := hEbd v (by rw [hinter]; exact inter_subset_right)
  have hW := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hV := (hcut.isPLCellOn_vertexBallImage hf₁ v).isPLBall_three
  obtain ⟨q, hq, -⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hY : IsPLBall 3 (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ v) :=
    isPLBall_union_of_inter_isPLBall_two hW hV (hinter ▸ ⟨q, hq⟩)
      (hinter ▸ hEw) (hinter ▸ hEv)
  obtain ⟨r, hr, -⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hDF : Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ v) := by
    intro y hy
    refine ⟨subset_closure (Or.inl
      ((hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset (hDS hy).1)), ?_⟩
    exact fun hi => (hDS hy).2.2 (interior_mono
      (union_subset (subset_iUnion _ w) (subset_iUnion _ v)) hi)
  exact ⟨w, v, e, B, B', Bb, Dj, Jd, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean, hwv, hewv, hwi, hvi, hei, hinter, hY, ⟨r, hr⟩, hDF,
    boundary_subset_frontier_union_of_inter_eq hW hV
      (hcut.isPLCellOn_splitDiskImage hf₁ e) hinter.symm hEw⟩

end DifferentialGeometry.Topology.PiecewiseLinear
