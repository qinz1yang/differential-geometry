/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSupport
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPlaneChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem exists_section34CompactBigonChart
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
      (B B' Bb Dj Jd O : Set E3) (k : OpenPartialHomeomorph E3 (Plane × ℝ)),
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
          section34CompactVertexBallImage src f₁ v) ∧
      IsOpen O ∧ Dj ⊆ O ∧
      O ∩ (⋃ z, section34CompactVertexBallImage src f₁ z) =
        O ∩ (section34CompactVertexBallImage src f₁ w ∪
          section34CompactVertexBallImage src f₁ v) ∧
      O ∩ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s =
        O ∩ (section34CompactVertexBallImage src f₁ w ∪
          section34CompactVertexBallImage src f₁ v) ∧
      Disjoint O (⋃ s' ≠ s, fbl s') ∧ Disjoint O (h '' section34CompactSimplexRim s.1) ∧
      (∀ e', e' ≠ e → Disjoint O (section34CompactSplitDiskImage src f₁ e')) ∧
      (∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
        O ⊆ interior (H t.1)) ∧
      (∀ z : Section34CompactVertexIndex K K', ¬ Section34Incident z.1 s.1 →
        Disjoint O (section34CompactVertexBallImage src f₁ z)) ∧
      Dj ⊆ k.source ∧ k.source ⊆ O ∧
      IsPiecewiseAffineOn k k.source ∧ IsPiecewiseAffineOn k.symm k.target ∧
      (∀ x ∈ k.source, x ∈ frontier (⋃ z, section34CompactVertexBallImage src f₁ z) ↔
        (k x).2 = 0) ∧
      (∀ x ∈ k.source, x ∈ ⋃ z, section34CompactVertexBallImage src f₁ z ↔ 0 ≤ (k x).2) ∧
      (∀ x ∈ k.source, x ∈ section34CompactFaceTorus
        (section34CompactVertexBallImage src f₁) s ↔ 0 ≤ (k x).2) ∧
      (∀ x ∈ k.source, x ∈ section34CompactSplitDiskImage srcBd f₁ e → (k x).2 = 0) := by
  classical
  obtain ⟨w, v, e, B, B', Bb, Dj, Jd, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean, hwv, hewv, hwi, hvi, hei, hinter, hY, hDball, hDF,
    hEfront⟩ := exists_section34CompactBigonBall hcut hgraph hinv s hop
  obtain ⟨-, hKfin, -⟩ := id hcut
  obtain ⟨-, hf₁, -, -, -, -, -, -, htorus, hVH, -⟩ := id hgraph
  obtain ⟨hfcell, -, -, -, -, -, -, -, -, -, -⟩ := id hinv
  have hDw : Dj ⊆ section34CompactVertexBallImage src f₁ w :=
    fun x hx => (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset (hDS hx).1
  have hDSg : Dj ⊆ frontier (⋃ z, section34CompactVertexBallImage src f₁ z) :=
    fun x hx => (hDS hx).2
  obtain ⟨O₀, hO₀, hDO₀, hO₀V, hO₀E, hO₀foreign⟩ :=
    exists_section34CompactBigonCarrier hcut hgraph hewv hwi hvi
      hD hDS hJ hBbe hBsplit hB'e
  have havoid : ∀ s', s' ≠ s → Disjoint Dj (fbl s') := by
    intro s' hs'
    exact section34CompactBigon_disjoint_other_faceBall hinv (Ne.symm hs') hB hBf hB'
      hB'e hBB' hD hDSg hJ (hclean s')
  let _ : Finite (Section34CompactSimplexIndex K 3) := finite_section34CompactSimplexIndex hKfin 3
  let _ : Finite (Section34CompactSimplexIndex K 4) := finite_section34CompactSimplexIndex hKfin 4
  let F := ⋃ s' ∈ {s' : Section34CompactSimplexIndex K 3 | s' ≠ s}, fbl s'
  have hFc : IsClosed F := (Set.toFinite _).isClosed_biUnion fun s' _ =>
    (hfcell s').isCompact.isClosed
  obtain ⟨S₁, S₂, hS₁, -, -, hS₁T, -, -, hspine⟩ := htorus s
  have hS₁c : IsCompact S₁ := by
    obtain ⟨φ⟩ := hS₁
    have : CompactSpace S₁ := φ.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hR : h '' section34CompactSimplexRim s.1 ⊆ S₁ := by
    obtain ⟨φ, p, -, hR⟩ := hspine
    rw [hR]
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hTunion : section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ⊆
      ⋃ z, section34CompactVertexBallImage src f₁ z := by
    intro x hx
    obtain ⟨a, _, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  let P := ⋂ t ∈ {t : Section34CompactSimplexIndex K 4 | Section34Incident s.1 t.1},
    interior (H t.1)
  have hP : IsOpen P := (Set.toFinite _).isOpen_biInter fun _ _ => isOpen_interior
  have hDP : Dj ⊆ P := by
    intro x hx
    refine mem_iInter₂.mpr fun t ht => ?_
    exact hVH w t.1 t.2.1 (hwi.trans (convexHull_min ht (convex_convexHull ℝ _)))
      (Or.inr (hDw hx))
  let O := O₀ ∩ ((F ∪ S₁)ᶜ ∩ P)
  have hO : IsOpen O := hO₀.inter ((hFc.union hS₁c.isClosed).isOpen_compl.inter hP)
  have hDO : Dj ⊆ O := by
    intro x hx
    refine ⟨hDO₀ hx, ?_, hDP hx⟩
    rintro (hxF | hxS₁)
    · obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.mp hxF
      exact disjoint_left.mp (havoid s' hs') hx hxs'
    · exact (hDSg hx).2 (interior_mono hTunion (hS₁T hxS₁))
  have hOV : O ∩ (⋃ z, section34CompactVertexBallImage src f₁ z) =
      O ∩ (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ v) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, ((Set.ext_iff.mp hO₀V x).mp ⟨hx.1.1, hx.2⟩).2⟩,
      fun hx => ⟨hx.1, ((Set.ext_iff.mp hO₀V x).mpr ⟨hx.1.1, hx.2⟩).2⟩⟩
  have hpairT : section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ v ⊆
        section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s := by
    intro x hx
    rcases hx with hxw | hxv
    · exact mem_iUnion₂.mpr ⟨⟨⟨s, w⟩, hwi⟩, rfl, hxw⟩
    · exact mem_iUnion₂.mpr ⟨⟨⟨s, v⟩, hvi⟩, rfl, hxv⟩
  have hOT : O ∩ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s =
      O ∩ (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ v) := by
    ext x
    exact ⟨fun hx => (Set.ext_iff.mp hOV x).mp ⟨hx.1, hTunion hx.2⟩,
      fun hx => ⟨hx.1, hpairT hx.2⟩⟩
  obtain ⟨k, hDk, hkO, hk, hki, hkS, hkY⟩ :=
    hY.exists_openPartialHomeomorph_boundary_disk_plane hDball hDF hO hDO
  let Y := section34CompactVertexBallImage src f₁ w ∪ section34CompactVertexBallImage src f₁ v
  have hlocalfront : frontier (⋃ z, section34CompactVertexBallImage src f₁ z) ∩ O =
      frontier Y ∩ O := by
    have heq : (⋃ z, section34CompactVertexBallImage src f₁ z) ∩ O = Y ∩ O :=
      (inter_comm _ _).trans (hOV.trans (inter_comm _ _))
    calc
      _ = frontier ((⋃ z, section34CompactVertexBallImage src f₁ z) ∩ O) ∩ O :=
        (frontier_inter_open_inter hO).symm
      _ = frontier (Y ∩ O) ∩ O := by rw [heq]
      _ = _ := frontier_inter_open_inter hO
  refine ⟨w, v, e, B, B', Bb, Dj, Jd, O, k, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean, hwv, hewv, hwi, hvi, hei, hinter, hY, hDball, hDF,
    hEfront, hO, hDO, hOV, hOT, ?_, ?_, ?_, ?_, ?_, hDk, hkO, hk, hki, ?_, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ hxO hxF => hxO.2.1 (Or.inl hxF)
  · exact disjoint_left.mpr fun _ hxO hxR => hxO.2.1 (Or.inr (hR hxR))
  · exact fun e' he' => (hO₀E e' he').mono_left inter_subset_left
  · exact fun t ht _ hx => mem_iInter₂.mp hx.2.2 t ht
  · exact fun z hz => (hO₀foreign z hz).mono_left inter_subset_left
  · intro x hx
    rw [← hkS x hx]
    exact ⟨fun h => ((Set.ext_iff.mp hlocalfront x).mp ⟨h, hkO hx⟩).1,
      fun h => ((Set.ext_iff.mp hlocalfront x).mpr ⟨h, hkO hx⟩).1⟩
  · intro x hx
    rw [← hkY x hx]
    exact ⟨fun h => ((Set.ext_iff.mp hOV x).mp ⟨hkO hx, h⟩).2,
      fun h => ((Set.ext_iff.mp hOV x).mpr ⟨hkO hx, h⟩).2⟩
  · intro x hx
    rw [← hkY x hx]
    exact ⟨fun h => ((Set.ext_iff.mp hOT x).mp ⟨hkO hx, h⟩).2,
      fun h => ((Set.ext_iff.mp hOT x).mpr ⟨hkO hx, h⟩).2⟩
  · exact fun x hx he => (hkS x hx).mp (hEfront he)

end DifferentialGeometry.Topology.PiecewiseLinear
