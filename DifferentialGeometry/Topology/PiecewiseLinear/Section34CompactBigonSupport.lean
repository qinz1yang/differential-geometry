/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3} {h : E3 → E3}
  {H : Finset E3 → Set E3} {tgtV : Section34CompactVertexIndex K K' → Set E3}
  {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
  {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem section34CompactBigon_disjoint_other_faceBall
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    {s s' : Section34CompactSimplexIndex K 3} (hss' : s ≠ s')
    {e : Section34CompactEdgeIndex K K'} {B B' Bb Dj Jd : Set E3}
    (hB : IsPLCellOn 1 B Bb) (hBf : B ⊆ fblBd s)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ tgtEBd e) (hBB' : B ∩ B' = Bb)
    (hD : IsPLCellOn 2 Dj Jd) (hDS : Dj ⊆ frontier (⋃ w, tgtV w))
    (hJ : Jd = B ∪ B') (hclean : Disjoint (Dj \ Jd) (fblBd s')) :
    Disjoint Dj (fbl s') := by
  obtain ⟨hfcell, -, -, hsep, -, hcross, -, -, -, -, -⟩ := hinv
  have hBD : B ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inl hx)
  have hB'D : B' ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inr hx)
  have hBavoid : Disjoint B (fbl s') := by
    refine disjoint_left.mpr fun x hxB hxf => ?_
    exact (hDS (hBD hxB)).2
      (hsep s s' hss' ⟨(hfcell s).boundary_subset (hBf hxB), hxf⟩)
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  obtain ⟨r, hr, hrBb⟩ := hB'.exists_isPLHomeomorphOn_stdSimplex
  have hrbd : r '' stdSimplexBoundary 1 = B' ∩ Bb := by
    rw [inter_eq_right.mpr hB'.boundary_subset, hrBb]
  obtain ⟨γ, hγ, hends⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hr hrbd
  rw [inter_eq_right.mpr hB'.boundary_subset] at hends
  let S := frontier (⋃ w, tgtV w)
  let A := fblBd s' ∩ S
  have hpair : A ∩ B' ⊆ Bb := by
    rw [← hends]
    apply inter_subset_endpoints_of_disk_boundary_crossing hq hDS hγ hB'e hB.isCompact.isClosed
    · exact hBB'.trans hends.symm
    · exact hqJ.symm.trans hJ
    · rw [← hqJ]
      exact hclean.mono_right inter_subset_left
    · exact fun x hx => hcross s' e x ⟨hx.1.1, hB'e hx.2⟩
  have hB'avoid : Disjoint B' (fblBd s') := by
    refine disjoint_left.mpr fun x hxB' hxBd => ?_
    have hxBb := hpair ⟨⟨hxBd, hDS (hB'D hxB')⟩, hxB'⟩
    exact disjoint_left.mp hBavoid (hB.boundary_subset hxBb)
      ((hfcell s').boundary_subset hxBd)
  have hDavoid : Disjoint Dj (fblBd s') := by
    refine disjoint_left.mpr fun x hxD hxBd => ?_
    by_cases hxJ : x ∈ Jd
    · rw [hJ] at hxJ
      rcases hxJ with hxB | hxB'
      · exact disjoint_left.mp hBavoid hxB ((hfcell s').boundary_subset hxBd)
      · exact disjoint_left.mp hB'avoid hxB' hxBd
    · exact disjoint_left.mp hclean ⟨hxD, hxJ⟩ hxBd
  have hfr : Disjoint Dj (frontier (fbl s')ᶜ) := by
    rw [frontier_compl, ← (hfcell s').boundary_eq_frontier]
    exact hDavoid
  obtain ⟨x, hxB⟩ := hB.nonempty
  have hsub : Dj ⊆ (fbl s')ᶜ := IsPreconnected.subset_of_disjoint_frontier
    hD.isConnected.isPreconnected
    ⟨x, hBD hxB, fun hxf => disjoint_left.mp hBavoid hxB hxf⟩ hfr
  exact disjoint_left.mpr fun x hxD hxf => hsub hxD hxf

end DifferentialGeometry.Topology.PiecewiseLinear
