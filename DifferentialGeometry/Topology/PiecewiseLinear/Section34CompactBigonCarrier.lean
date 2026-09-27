/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem exists_section34CompactBigonCarrier
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {s : Section34CompactSimplexIndex K 3} {w v : Section34CompactVertexIndex K K'}
    {e : Section34CompactEdgeIndex K K'} {B B' Bb Dj Jd : Set E3}
    (hewv : (e.1 : Set E3) = (w.1 : Set E3) ∪ (v.1 : Set E3))
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
      frontier (⋃ z, section34CompactVertexBallImage src f₁ z))
    (hJ : Jd = B ∪ B') (hBbe : Bb ⊆ section34CompactSplitDiskImage srcBd f₁ e)
    (hBsplit : B ∩ (⋃ e', section34CompactSplitDiskImage src f₁ e') = Bb)
    (hB'e : B' ⊆ section34CompactSplitDiskImage srcBd f₁ e) :
    ∃ O : Set E3, IsOpen O ∧ Dj ⊆ O ∧
      O ∩ (⋃ z, section34CompactVertexBallImage src f₁ z) =
        O ∩ (section34CompactVertexBallImage src f₁ w ∪
          section34CompactVertexBallImage src f₁ v) ∧
      (∀ e', e' ≠ e → Disjoint O (section34CompactSplitDiskImage src f₁ e')) ∧
      (∀ z : Section34CompactVertexIndex K K', ¬ Section34Incident z.1 s.1 →
        Disjoint O (section34CompactVertexBallImage src f₁ z)) := by
  classical
  obtain ⟨-, -, hK'fin, -, -, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hends, -⟩ := id hcut
  obtain ⟨-, hf₁, -, -, -, -, -, -, -, -, -⟩ := hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  have hDw : Dj ⊆ section34CompactVertexBallImage src f₁ w :=
    fun x hx => (hVcell w).boundary_subset (hDS hx).1
  have hW := (hVcell w).isPLBall_three
  obtain ⟨p, hp, hpb⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hDsurface : Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w) := by
    rw [← (hVcell w).boundary_eq_frontier]
    exact fun x hx => (hDS hx).1
  have hDinter : ∀ e', Dj ∩ section34CompactSplitDiskImage src f₁ e' ⊆ Jd := by
    intro e' x hx
    have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hx.2 (hDw hx.1)
    obtain ⟨a, b, -, heab, hEab⟩ := hends e'
    have hEwsrc : src (.splitDisk e') ⊆ src (.vertexBall w) := by
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e' heab hwe with rfl | rfl
      · rw [hEab]
        exact inter_subset_left
      · rw [hEab]
        exact inter_subset_right
    have hEw : section34CompactSplitDiskImage src f₁ e' ⊆
        frontier (section34CompactVertexBallImage src f₁ w) := by
      rw [← (hVcell w).boundary_eq_frontier]
      refine image_mono fun y hy => ?_
      rw [hbd (.vertexBall w)]
      exact mem_iUnion₂.mpr ⟨.splitDisk e', ⟨hEwsrc, by simp⟩, hy⟩
    obtain ⟨q, hq, hqb⟩ := (hEcell e').exists_isPLHomeomorphOn_stdSimplex
    have hcore : section34CompactSplitDiskImage src f₁ e' \ q '' stdSimplexBoundary 2 ⊆
        frontier (section34CompactVertexBallImage src f₁ w) \ Dj := by
      rintro y ⟨hy, hyb⟩
      refine ⟨hEw hy, fun hyD => ?_⟩
      exact (hDS hyD).2.2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ e'
        ⟨hy, fun h => hyb (hqb ▸ h)⟩)
    have hEcl : section34CompactSplitDiskImage src f₁ e' ⊆
        closure (frontier (section34CompactVertexBallImage src f₁ w) \ Dj) := by
      rw [← hq.closure_sdiff_image_stdSimplexBoundary]
      exact closure_mono hcore
    rw [hpb, ← hW.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
      hp hDsurface]
    exact ⟨hx.1, hEcl hx.2⟩
  have hDavoid : ∀ e', e' ≠ e → Disjoint Dj (section34CompactSplitDiskImage src f₁ e') := by
    intro e' he
    refine disjoint_left.mpr fun x hxD hxe' => ?_
    have hxJ := hDinter e' ⟨hxD, hxe'⟩
    have hxe : x ∈ section34CompactSplitDiskImage src f₁ e := by
      apply (hEcell e).boundary_subset
      rw [hJ] at hxJ
      rcases hxJ with hxB | hxB'
      · exact hBbe (hBsplit ▸ ⟨hxB, mem_iUnion.mpr ⟨e', hxe'⟩⟩)
      · exact hB'e hxB'
    exact disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁ he) hxe' hxe
  have hDvertices : ∀ z, z ≠ w → z ≠ v → Disjoint Dj
      (section34CompactVertexBallImage src f₁ z) := by
    intro z hzw hzv
    refine disjoint_left.mpr fun x hxD hxz => ?_
    obtain ⟨e', hxe'⟩ :=
      hcut.exists_mem_splitDiskImage_of_ne hf₁ (Ne.symm hzw) (hDw hxD) hxz
    have he : e' = e := by
      by_contra he
      exact disjoint_left.mp (hDavoid e' he) hxD hxe'
    subst e'
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e hewv
      (hcut.subset_of_mem_splitDiskImage hf₁ hxe' hxz) with hzw' | hzv'
    · exact hzw hzw'
    · exact hzv hzv'
  let _ : Finite (Section34CompactVertexIndex K K') :=
    finite_section34CompactGraphIndex hK'fin _ 1
  let _ : Finite (Section34CompactEdgeIndex K K') :=
    finite_section34CompactGraphIndex hK'fin _ 2
  let A := ⋃ z ∈ {z : Section34CompactVertexIndex K K' | z ≠ w ∧ z ≠ v},
    section34CompactVertexBallImage src f₁ z
  let E := ⋃ e' ∈ {e' : Section34CompactEdgeIndex K K' | e' ≠ e},
    section34CompactSplitDiskImage src f₁ e'
  have hAc : IsClosed A := (Set.toFinite _).isClosed_biUnion fun z _ =>
    (hVcell z).isCompact.isClosed
  have hEc : IsClosed E := (Set.toFinite _).isClosed_biUnion fun e' _ =>
    (hEcell e').isCompact.isClosed
  let O := (A ∪ E)ᶜ
  have hDO : Dj ⊆ O := by
    intro x hx
    rintro (hxA | hxE)
    · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxA
      exact disjoint_left.mp (hDvertices z hz.1 hz.2) hx hxz
    · obtain ⟨e', he', hxe'⟩ := mem_iUnion₂.mp hxE
      exact disjoint_left.mp (hDavoid e' he') hx hxe'
  have hOvertices : ∀ x ∈ O, ∀ z, x ∈ section34CompactVertexBallImage src f₁ z →
      z = w ∨ z = v := by
    intro x hx z hxz
    by_contra hz
    exact hx (Or.inl (mem_iUnion₂.mpr ⟨z, ⟨fun h => hz (Or.inl h),
      fun h => hz (Or.inr h)⟩, hxz⟩))
  refine ⟨O, (hAc.union hEc).isOpen_compl, hDO, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hxO, hxV⟩
      obtain ⟨z, hxz⟩ := mem_iUnion.mp hxV
      refine ⟨hxO, ?_⟩
      rcases hOvertices x hxO z hxz with rfl | rfl
      · exact Or.inl hxz
      · exact Or.inr hxz
    · exact inter_subset_inter_right O
        (union_subset (subset_iUnion _ w) (subset_iUnion _ v))
  · intro e' he'
    exact disjoint_left.mpr fun x hxO hxe' => hxO
      (Or.inr (mem_iUnion₂.mpr ⟨e', he', hxe'⟩))
  · intro z hz
    refine disjoint_left.mpr fun x hxO hxz => ?_
    rcases hOvertices x hxO z hxz with rfl | rfl
    · exact hz hwi
    · exact hz hvi

end DifferentialGeometry.Topology.PiecewiseLinear
