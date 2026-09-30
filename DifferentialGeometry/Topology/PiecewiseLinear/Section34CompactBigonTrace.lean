/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceArcNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {H : Finset E3 → Set E3}

theorem compactBigon_inter_faceBall_boundary
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    {s : Section34CompactSimplexIndex K 3} {e : Section34CompactEdgeIndex K K'}
    {B B' Bb Dj Jd : Set E3} (hB : IsPLCellOn 1 B Bb) (hBf : B ⊆ fblBd s)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ section34CompactSplitDiskImage srcBd f₁ e)
    (hBB' : B ∩ B' = Bb) (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hJ : Jd = B ∪ B') (hclean : Disjoint (Dj \ Jd) (fblBd s)) :
    Dj ∩ fblBd s = B := by
  obtain ⟨-, -, -, -, -, hcross, -⟩ := id hinv
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  obtain ⟨r, hr, hrBb⟩ := hB'.exists_isPLHomeomorphOn_stdSimplex
  have hrbd : r '' stdSimplexBoundary 1 = B' ∩ Bb := by
    rw [inter_eq_right.mpr hB'.boundary_subset, hrBb]
  obtain ⟨γ, hγ, hends⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hr hrbd
  rw [inter_eq_right.mpr hB'.boundary_subset] at hends
  let S := frontier (⋃ w, section34CompactVertexBallImage src f₁ w)
  have hpair : (fblBd s ∩ S) ∩ B' ⊆ Bb := by
    rw [← hends]
    refine inter_subset_endpoints_of_disk_boundary_crossing hq (S := S)
      (B := section34CompactSplitDiskImage srcBd f₁ e) (F := B)
      hDS hγ hB'e hB.isCompact.isClosed ?_ ?_ ?_ ?_
    · exact hBB'.trans hends.symm
    · rw [← hqJ, hJ]
    · rw [← hqJ]
      exact hclean.mono_right inter_subset_left
    · intro x hx
      exact hcross s e x ⟨hx.1.1, hB'e hx.2⟩
  apply subset_antisymm
  · rintro x ⟨hxD, hxBd⟩
    have hxJ : x ∈ Jd := by
      by_contra hxJ
      exact disjoint_left.mp hclean ⟨hxD, hxJ⟩ hxBd
    rw [hJ] at hxJ
    exact hxJ.elim id (fun hxB' => hB.boundary_subset (hpair ⟨⟨hxBd, hDS hxD⟩, hxB'⟩))
  · exact fun x hx => ⟨hD.boundary_subset (hJ.symm ▸ Or.inl hx), hBf hx⟩

theorem compactBigon_inter_splitDisk_boundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {w : Section34CompactVertexIndex K K'} {e : Section34CompactEdgeIndex K K'}
    {B B' Bb Dj Jd : Set E3}
    (hBsplit : B ∩ (⋃ e', section34CompactSplitDiskImage src f₁ e') = Bb)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ section34CompactSplitDiskImage srcBd f₁ e)
    (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
      frontier (⋃ w', section34CompactVertexBallImage src f₁ w')) (hJ : Jd = B ∪ B') :
    Dj ∩ section34CompactSplitDiskImage srcBd f₁ e = B' := by
  obtain ⟨-, -, -, -, -, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hends, -⟩ := id hcut
  obtain ⟨-, hf₁, -⟩ := id hgraph
  have hW := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hDw : Dj ⊆ section34CompactVertexBallImage src f₁ w :=
    fun x hx => hW.boundary_subset (hDS hx).1
  obtain ⟨p, hp, hpb⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hDsurface : Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w) := by
    rw [← hW.boundary_eq_frontier]
    exact fun x hx => (hDS hx).1
  have hDinter : Dj ∩ section34CompactSplitDiskImage src f₁ e ⊆ Jd := by
    intro x hx
    have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hx.2 (hDw hx.1)
    obtain ⟨a, b, -, heab, hEab⟩ := hends e
    have hEwsrc : src (.splitDisk e) ⊆ src (.vertexBall w) := by
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e heab hwe with rfl | rfl
      · rw [hEab]
        exact inter_subset_left
      · rw [hEab]
        exact inter_subset_right
    have hEw : section34CompactSplitDiskImage src f₁ e ⊆
        section34CompactVertexBallImage srcBd f₁ w := by
      refine image_mono fun y hy => ?_
      rw [hbd (.vertexBall w)]
      exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hEwsrc, by simp⟩, hy⟩
    obtain ⟨q, hq, hqb⟩ := hE.exists_isPLHomeomorphOn_stdSimplex
    have hcore : section34CompactSplitDiskImage src f₁ e \ q '' stdSimplexBoundary 2 ⊆
        frontier (section34CompactVertexBallImage src f₁ w) \ Dj := by
      rw [← hqb, ← hW.boundary_eq_frontier]
      intro y hy
      exact ⟨hEw hy.1, fun hyD => (hDS hyD).2.2
        (hcut.splitDiskImage_sdiff_subset_interior hf₁ e hy)⟩
    have hEcl : section34CompactSplitDiskImage src f₁ e ⊆
        closure (frontier (section34CompactVertexBallImage src f₁ w) \ Dj) := by
      rw [← hq.closure_sdiff_image_stdSimplexBoundary]
      exact closure_mono hcore
    have hboundary := hW.isPLBall_three.isPLSphere_frontier
    rw [hpb, ← hboundary.inter_closure_sdiff_eq_image_stdSimplexBoundary hp hDsurface]
    exact ⟨hx.1, hEcl hx.2⟩
  apply subset_antisymm
  · rintro x ⟨hxD, hxe⟩
    have hxJ := hDinter ⟨hxD, hE.boundary_subset hxe⟩
    rw [hJ] at hxJ
    exact hxJ.elim (fun hxB => hB'.boundary_subset
      (hBsplit ▸ ⟨hxB, mem_iUnion.mpr ⟨e, hE.boundary_subset hxe⟩⟩)) id
  · exact fun x hx => ⟨hD.boundary_subset (hJ.symm ▸ Or.inr hx), hB'e hx⟩

theorem exists_compactBigonTraceArc (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3) {B Bb Dj O : Set E3}
    (hB : IsPLCellOn 1 B Bb) (hDB : Dj ∩ fblBd s = B)
    (hDS : Dj ⊆ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hO : IsOpen O) (hDO : Dj ⊆ O) :
    ∃ (A : Set E3) (q : (Fin 2 → ℝ) → E3) (W : Set E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
      A ⊆ (fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) ∩ O ∧
      Dj ∩ A = B ∧ Disjoint Dj (q '' stdSimplexBoundary 1) ∧
      IsOpen W ∧ Dj ⊆ W ∧ W ⊆ O ∧
      W ∩ (fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) = W ∩ A := by
  obtain ⟨-, -, hK'fin, -⟩ := id hcut
  let _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  obtain ⟨-, hf₁, -⟩ := id hgraph
  obtain ⟨hfcell, -, -, -, hcross, -⟩ := id hinv
  let X := ⋃ w, section34CompactVertexBallImage src f₁ w
  have hX : IsPolyhedron X := IsPolyhedron.iUnion fun w =>
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three.isPolyhedron
  have hreg : X ⊆ closure (interior X) := by
    intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    have hW := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
    have hcl : x ∈ closure (interior (section34CompactVertexBallImage src f₁ w)) := by
      rw [hW.closure_interior_of_finrank (by simp)]
      exact hw
    exact closure_mono (interior_mono (subset_iUnion _ w)) hcl
  have hF : IsPLSphere 2 (fblBd s) := by
    rw [(hfcell s).boundary_eq_frontier]
    exact (hfcell s).isPLBall_three.isPLSphere_frontier
  obtain ⟨b, hb, -⟩ := hB.exists_isPLHomeomorphOn_stdSimplex
  have hDF : Dj ∩ (fblBd s ∩ frontier X) = B := by
    rw [← hDB]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hDS hx.1⟩⟩
  exact hF.exists_arc_neighborhood_of_crossing_trace hX hreg (hcross s) ⟨b, hb⟩ hDF hO hDO

theorem exists_compactBigonSplittingArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {e : Section34CompactEdgeIndex K K'} {B' Bb Dj O : Set E3}
    (hB' : IsPLCellOn 1 B' Bb)
    (hDB' : Dj ∩ section34CompactSplitDiskImage srcBd f₁ e = B')
    (hO : IsOpen O) (hDO : Dj ⊆ O) :
    ∃ (A : Set E3) (q : (Fin 2 → ℝ) → E3) (W : Set E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
      A ⊆ section34CompactSplitDiskImage srcBd f₁ e ∩ O ∧
      Dj ∩ A = B' ∧ Disjoint Dj (q '' stdSimplexBoundary 1) ∧
      IsOpen W ∧ Dj ⊆ W ∧ W ⊆ O ∧
      W ∩ section34CompactSplitDiskImage srcBd f₁ e = W ∩ A := by
  obtain ⟨-, hf₁, -⟩ := id hgraph
  have hcircle := (hcut.isPLCellOn_splitDiskImage hf₁ e).isPLSphere_one_of_two
  obtain ⟨b, hb, -⟩ := hB'.exists_isPLHomeomorphOn_stdSimplex
  have hDF : Dj ∩ (⋃ _ : Unit, section34CompactSplitDiskImage srcBd f₁ e) = B' := by
    rwa [iUnion_const]
  obtain ⟨A, q, W, hq, hA, hDA, hends, hW, hDW, hWO, hWA⟩ :=
    exists_arc_neighborhood_of_finite_circle_union
      (fun _ : Unit => section34CompactSplitDiskImage srcBd f₁ e) (fun _ => hcircle)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim) ⟨b, hb⟩ hDF hO hDO
  simp only [iUnion_const] at hA hWA
  exact ⟨A, q, W, hq, hA, hDA, hends, hW, hDW, hWO, hWA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
