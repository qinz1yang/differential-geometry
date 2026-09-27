/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.OutermostCircleCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPuncturedSphere
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexOperations

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}
  {H : Finset E3 → Set E3}
  {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_compact_vertex_return_arc_of_torus_disk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J Δ : Set E3}
    (hJ : IsPLSphere 1 J)
    (hJcomp : J ∈ section34CompactTraceComponents
      (section34CompactVertexBallImage src f₁) fblBd s)
    (hΔ : IsPLCellOn 2 Δ J)
    (hΔT : Δ ⊆ frontier (section34CompactFaceTorus
      (section34CompactVertexBallImage src f₁) s)) :
    ∃ (w : Section34CompactVertexIndex K K')
      (e : Section34CompactEdgeIndex K K') (B : Set E3) (η : ℝ → E3),
      IsPLHomeomorphOn η (Icc 0 1) B ∧
      B ⊆ J ∧
      B ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
      ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ e' : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage src f₁ e') = {η 0, η 1} := by
  classical
  have hf₁ := hgraph.2.1
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  have hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    obtain ⟨x, _, hxJ⟩ := hJcomp
    rw [← hxJ]
    exact connectedComponentIn_subset _ _
  let I := {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}
  let G : I → Set E3 := fun e => section34CompactSplitDiskImage srcBd f₁ e.1
  have hG : ∀ i, IsPLSphere 1 (G i) :=
    fun i => (hcut.isPLCellOn_splitDiskImage hf₁ i.1).isPLSphere_one_of_two
  obtain ⟨q, hq, hqJ⟩ := hΔ.exists_isPLHomeomorphOn_stdSimplex
  have hγ : ∀ x ∈ J, ∀ e : Section34CompactEdgeIndex K K',
      x ∈ section34CompactSplitDiskImage src f₁ e →
        x ∈ section34CompactSplitDiskImage srcBd f₁ e := by
    intro x hx e hxe
    by_contra hxγ
    exact (hJT hx).2.2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hxe, hxγ⟩)
  have hinc : ∀ x ∈ J, ∀ e : Section34CompactEdgeIndex K K',
      x ∈ section34CompactSplitDiskImage src f₁ e → Section34Incident e.1 s.1 := by
    intro x hx e hxe
    by_contra he
    exact Set.disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s e he)
      ((hinv.1 s).boundary_subset (hJT hx).1) hxe
  have hmeet : (J ∩ ⋃ i, G i).Nonempty := by
    by_contra hempty
    have hJE : ∀ e : Section34CompactEdgeIndex K K',
        Disjoint J (section34CompactSplitDiskImage src f₁ e) := by
      intro e
      apply Set.disjoint_left.mpr
      intro x hx hxe
      exact hempty ⟨x, hx, mem_iUnion.mpr ⟨⟨e, hinc x hx e hxe⟩, hγ x hx e hxe⟩⟩
    have hN : IsClosed (⋃ w, section34CompactVertexBallImage src f₁ w) :=
      isClosed_iUnion_of_finite fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed
    obtain ⟨w, hw⟩ := hcut.exists_vertex_ball_of_connected_avoiding_split_disks hf₁ hJ.isConnected
      (fun x hx => hN.frontier_subset (hJT hx).2) hJE
    exact hinv.not_circle_subset_vertexBall_of_no_compression hcut hgraph hnc s w hJ
      (fun x hx => (hJT hx).1) (fun x hx => (hJT hx).2) hw
  have hGΘ : ∀ i, G i ⊆ frontier
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro i x hx
    exact ((hcut.splitDiskImage_faceTorus_boundary hf₁ s i.1 i.2).2.1.symm.subset hx).1
  have hno : ∀ i, ¬ G i ⊆ Δ := by
    intro i hi
    obtain ⟨D, r, hr, hDΔ, hrG⟩ := hq.exists_disk_subset_of_circle_subset (hG i) hi
    exact (hcut.splitDiskBoundary_is_essential hf₁ s i.1 i.2).2
      ⟨D, r, hr, hDΔ.trans hΔT, hrG.symm⟩
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    exact (hcut.disjoint_splitDiskImage hf₁ (fun heq => hij (Subtype.ext heq))).mono
      (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset
      (hcut.isPLCellOn_splitDiskImage hf₁ j.1).boundary_subset
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  obtain ⟨L, hLfin, hL, -, hLΘ⟩ := hT.isPLTorus_frontier.exists_combinatorial_triangulation
  have : Finite L.faces := hLfin.to_subtype
  obtain ⟨-, -, -, -, -, -, -, hfinite, -⟩ := id hinv
  have hfin : (J ∩ ⋃ i, G i).Finite := (hfinite s).subset (by
    rintro x ⟨hxJ, hxG⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxG
    exact ⟨(hJT hxJ).1, mem_iUnion.mpr ⟨i.1, hxi⟩⟩)
  have hcross : ∀ i, ∀ x ∈ J ∩ G i, HasPLCurveCrossingOnAt L.space J (G i) x := by
    intro i x hx
    rw [hLΘ]
    exact hinv.curve_crossing_on_face_torus hcut hf₁ s hJ hJT i.1 hx
  obtain ⟨i, B, η, hη, hBJ, hends, hBG⟩ :=
    exists_boundary_arc_avoiding_disjoint_circles L hL hq hqJ.symm
      (hΔT.trans hLΘ.symm.subset) hG (fun i => (hGΘ i).trans hLΘ.symm.subset)
      hGdis hfin hno hcross hmeet
  have hBE : B ∩ (⋃ e, section34CompactSplitDiskImage src f₁ e) = {η 0, η 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxE⟩
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hxE
      exact hBG.subset ⟨hxB, mem_iUnion.mpr
        ⟨⟨e, hinc x (hBJ hxB) e hxe⟩, hγ x (hBJ hxB) e hxe⟩⟩
    · intro x hx
      exact ⟨(pair_subset (hη.bijOn.mapsTo (by norm_num))
        (hη.bijOn.mapsTo (by norm_num))) hx,
        mem_iUnion.mpr ⟨i.1, (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset (hends hx)⟩⟩
  obtain ⟨w, hw⟩ := hcut.exists_vertex_boundary_of_arc_avoiding_split_disks hf₁ hη
    (fun x hx => (hJT (hBJ hx)).2) (by
      intro e
      apply Set.disjoint_left.mpr
      rintro x ⟨hxB, hxends⟩ hxe
      exact hxends (hBE.subset ⟨hxB, mem_iUnion.mpr ⟨e, hxe⟩⟩))
  exact ⟨w, i.1, B, η, hη, hBJ, hw, hends, hBE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
