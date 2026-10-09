/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualOuterDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Helpers

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.frontier_sdiff_iUnion_eq_of_patch
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (Rf : Section34CompactSimplexIndex K 4 → Set E3) (w : Section34CompactVertexIndex K K') :
    frontier (section34CompactVertexBallImage src f₁ w) \
        ((⋃ e, section34CompactSplitDiskImage src f₁ e) ∪
          ⋃ x : Section34CompactPatchIndex K K',
            Rf x.1.1 ∩ section34CompactVertexBallImage src f₁ x.1.2) =
      frontier (section34CompactVertexBallImage src f₁ w) \
        ((⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
          section34CompactSplitDiskImage src f₁ e) ∪
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
          Rf t ∩ section34CompactVertexBallImage src f₁ w) := by
  have hVc : IsClosed (section34CompactVertexBallImage src f₁ w) :=
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed
  apply Subset.antisymm
  · rintro z ⟨hzS, hzn⟩
    refine ⟨hzS, fun hz => hzn ?_⟩
    rcases hz with hz | hz
    · obtain ⟨e, -, hze⟩ := mem_iUnion₂.mp hz
      exact Or.inl (mem_iUnion.mpr ⟨e, hze⟩)
    · obtain ⟨t, ht, hzR, hzV⟩ := mem_iUnion₂.mp hz
      exact Or.inr (mem_iUnion.mpr ⟨⟨(t, w), ht⟩, hzR, hzV⟩)
  · rintro z ⟨hzS, hzn⟩
    have hzV : z ∈ section34CompactVertexBallImage src f₁ w := hVc.frontier_subset hzS
    refine ⟨hzS, fun hz => hzn ?_⟩
    rcases hz with hz | hz
    · obtain ⟨e, hze⟩ := mem_iUnion.mp hz
      exact Or.inl (mem_iUnion₂.mpr ⟨e, hcut.subset_of_mem_splitDiskImage hf₁ hze hzV, hze⟩)
    · obtain ⟨x, hzR, hzx⟩ := mem_iUnion.mp hz
      by_cases hxw : x.1.2 = w
      · refine Or.inr (mem_iUnion₂.mpr ⟨x.1.1, ?_, hzR, hzV⟩)
        rw [← hxw]
        exact x.2
      · obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ (Ne.symm hxw) hzV hzx
        exact Or.inl (mem_iUnion₂.mpr ⟨e, hcut.subset_of_mem_splitDiskImage hf₁ hze hzV, hze⟩)

theorem Section34CompactCutFrame.splitDiskImage_boundary_sdiff_iUnion_eq
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (Rf : Section34CompactSimplexIndex K 4 → Set E3) (e : Section34CompactEdgeIndex K K') :
    section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ i : Section34CompactEdgeArcIndex K K',
          Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2 =
      section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
  have hEbE := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  apply Subset.antisymm
  · rintro z ⟨hzb, hzn⟩
    refine ⟨hzb, fun hz => hzn ?_⟩
    obtain ⟨t, het, hzR, hzE⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion.mpr ⟨⟨(t, e), het⟩, hzR, hzE⟩
  · rintro z ⟨hzb, hzn⟩
    refine ⟨hzb, fun hz => hzn ?_⟩
    obtain ⟨i, hzR, hzE⟩ := mem_iUnion.mp hz
    by_cases hie : i.1.2 = e
    · refine mem_iUnion₂.mpr ⟨i.1.1, ?_, hzR, ?_⟩
      · rw [← hie]
        exact i.2
      · rw [← hie]
        exact hzE
    · exact absurd (hEbE hzb) (Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁ hie) hzE)

end Helpers

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactResidualBalls (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (htrace : Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd)
    {tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP) :
    ∃ (tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))),
      Section34CompactResidualPlus K K' H (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) tgtD tgtA tgtP tgtR tgtRBd tgtX tgtXBd
        tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd := by
  let _ := htrace
  obtain ⟨-, hKfin, -⟩ := id hcut
  have _ := finite_section34CompactSimplexIndex hKfin 4
  obtain ⟨-, hf₁, -, -, hcore, -, -, -, -, hHt, -⟩ := id hgraph
  obtain ⟨hfbl, -, -, -, -, -, -, -, -, hfblH, hext⟩ := id hinv
  obtain ⟨-, -, hHcell⟩ := id hcar
  obtain ⟨-, hD2, -, -, -, -, -, -, hP9, -⟩ := id hdisk
  have hDfbl : ∀ s, tgtD s ⊆ fbl s := fun s => (hD2 s).trans (hfbl s).boundary_subset
  choose Rf hR hDR hfr hint hio using fun t => hcut.exists_residualBall hf₁ hdisk t
  have h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅ :=
    fun t w hw => hcut.residual_inter_vertexBallImage_eq_empty hf₁ hdisk hext hDfbl hcore (hR t)
      (hfr t) (hint t) hw
  have h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅ := fun t s hs =>
    hcut.residual_inter_faceDisk_eq_empty hf₁ hdisk (hR t) (hfr t) (hint t) (h7 t) hs
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  refine ⟨Rf, fun t => frontier (Rf t),
    fun x => Rf x.1.1 ∩ section34CompactVertexBallImage src f₁ x.1.2,
    fun x => (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1), tgtA a) ∪
      ⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
        Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2,
    fun i => Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2,
    fun i => ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1), tgtP p,
    fun o => closure (section34CompactVertexBallImage srcBd f₁ o.1 \
      ((⋃ e, section34CompactSplitDiskImage src f₁ e) ∪
        ⋃ x : Section34CompactPatchIndex K K',
          Rf x.1.1 ∩ section34CompactVertexBallImage src f₁ x.1.2)),
    fun o => (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = o.1 ∧
        convexHull ℝ (a.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtA a) ∪
      ⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : o.1.1 ⊆ q.1.1),
        closure (section34CompactSplitDiskImage srcBd f₁ q.1 \
          ⋃ i : Section34CompactEdgeArcIndex K K',
            Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2),
    fun q => closure (section34CompactSplitDiskImage srcBd f₁ q.1 \
      ⋃ i : Section34CompactEdgeArcIndex K K',
        Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2),
    fun q => ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = q.1 ∧
        convexHull ℝ (p.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtP p, ?_⟩
  unfold Section34CompactResidualPlus
  beta_reduce
  refine ⟨fun t => (hR t).isPLCellOn_frontier, fun x => ?_, fun i => ?_, fun o => ?_, fun q => ?_,
    fun x => rfl, h7, fun t s hs => ?_, h9, fun t t' htt => ?_, fun i => rfl, fun t e he => ?_,
    fun i => ?_, fun t => ?_, fun i => rfl, fun x => rfl, fun i p hpi hpI => ?_, fun t => ?_,
    fun o => rfl, fun q => rfl, fun w => ?_, fun e => ?_, fun o => rfl, fun q => rfl⟩
  · obtain ⟨q, hq, hqb⟩ := hcut.exists_residualPatch_boundary hf₁ hdisk (hR x.1.1) (hDR x.1.1)
      (hfr x.1.1) (hint x.1.1) (hio x.1.1) (h7 x.1.1) x.2
    have hU : (⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
        Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2) =
        ⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1),
          Rf x.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2 :=
      iUnion₂_congr fun i hi => by rw [hi.1]
    rw [hU, ← hqb]
    exact isPLCellOn_id_of_isPLBall hq
  · obtain ⟨γ, hγ, hγb⟩ := hcut.exists_residualEdgeArc hf₁ hdisk (hR i.1.1) (hDR i.1.1)
      (hfr i.1.1) (hint i.1.1) (hio i.1.1) (h7 i.1.1) i.2
    rw [← hγb]
    exact isPLCellOn_one_of_isPLHomeomorphOn_Icc hγ
  · obtain ⟨q, hq, hqb⟩ := hcut.exists_residual_outerDisk hf₁ hdisk hR hDR hfr hint hio h7 h9
      o.1 o.2
    rw [(hcut.isPLCellOn_vertexBallImage hf₁ o.1).boundary_eq_frontier,
      hcut.frontier_sdiff_iUnion_eq_of_patch hf₁ Rf o.1]
    have hQ : (⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : o.1.1 ⊆ q.1.1),
        closure (section34CompactSplitDiskImage srcBd f₁ q.1 \
          ⋃ i : Section34CompactEdgeArcIndex K K',
            Rf i.1.1 ∩ section34CompactSplitDiskImage src f₁ i.1.2)) =
        ⋃ (e : Section34CompactEdgeIndex K K')
          (_ : convexHull ℝ (e.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space ∧
            o.1.1 ⊆ e.1),
          closure (section34CompactSplitDiskImage srcBd f₁ e \
            ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
              Rf t ∩ section34CompactSplitDiskImage src f₁ e) := by
      ext y
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨q, hq, hy⟩
        rw [hcut.splitDiskImage_boundary_sdiff_iUnion_eq hf₁ Rf q.1] at hy
        exact ⟨q.1, ⟨q.2, hq⟩, hy⟩
      · rintro ⟨e, ⟨heb, he⟩, hy⟩
        refine ⟨⟨e, heb⟩, he, ?_⟩
        rw [hcut.splitDiskImage_boundary_sdiff_iUnion_eq hf₁ Rf e]
        exact hy
    rw [hQ, ← hqb]
    exact isPLCellOn_id_of_isPLBall hq
  · obtain ⟨δ, hδ, hδb⟩ := hcut.exists_residual_outerArc hf₁ hdisk hR hDR hfr hint hio h7 h9
      q.1 q.2
    rw [hcut.splitDiskImage_boundary_sdiff_iUnion_eq hf₁ Rf q.1, ← hδb]
    exact isPLCellOn_one_of_isPLHomeomorphOn_Icc hδ
  · exact inter_eq_right.mpr fun z hz =>
      (hR t).isPolyhedron.isClosed.frontier_subset (hDR t s hs hz)
  · exact hcut.residual_inter_residual_subset hf₁ hdisk hR hDR hfr hint h7 h9 htt
  · exact hcut.residual_inter_splitDiskImage_eq_empty hf₁ (h7 t) he
  · exact hcut.residual_inter_splitDiskImage_subset hf₁ (hR i.1.1) (hint i.1.1) (h7 i.1.1) i.1.2
  · apply Subset.antisymm
    · intro z hz
      rcases hfr t hz with hz' | hz'
      · obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hz'
        exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, w), hw⟩, rfl,
          (hR t).isPolyhedron.isClosed.frontier_subset hz, hzw⟩)
      · exact Or.inl hz'
    · rintro z (hz | hz)
      · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz
        exact hDR t s hs hzs
      · obtain ⟨x, hxt, hzR, hzV⟩ := mem_iUnion₂.mp hz
        rw [hxt] at hzR
        refine ⟨subset_closure hzR, fun hzi => ?_⟩
        have hxw : Section34Incident x.1.2.1 t.1 := by
          rw [← hxt]
          exact x.2
        exact Set.disjoint_left.mp (hint t) hzi (mem_iUnion₂.mpr ⟨x.1.2, hxw, hzV⟩)
  · by_cases hpt : Section34Incident p.1.1.1 i.1.1.1
    · exact subset_iUnion₂_of_subset p ⟨hpi, hpt⟩ subset_rfl
    · exfalso
      obtain ⟨z, hz⟩ := (hP9 p).nonempty
      have hzD : z ∈ tgtD p.1.1 :=
        ((hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁ p).symm.subset hz).1
      have h0 : z ∈ Rf i.1.1 ∩ tgtD p.1.1 := ⟨(hpI hz).1, hzD⟩
      rw [h9 i.1.1 p.1.1 hpt] at h0
      exact h0
  · refine ((hHcell t.1 t.2.1).isPLBall_three).subset_of_isCompact_frontier_subset
      (hR t).isPolyhedron.isCompact fun z hz => ?_
    rcases hfr t hz with hz' | hz'
    · obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hz'
      exact interior_subset ((hHt w t.1 t.2.1 hw) (Or.inr hzw))
    · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz'
      exact interior_subset (hfblH s t hs (hDfbl s hzs))
  · rw [(hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier]
    apply Subset.antisymm
    · intro z hz
      have hsplit : z ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
          section34CompactSplitDiskImage src f₁ e) ∪
          ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
            Rf t ∩ section34CompactVertexBallImage src f₁ w →
          z ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
            section34CompactSplitDiskImage src f₁ e) ∪
            ⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.2 = w),
              Rf x.1.1 ∩ section34CompactVertexBallImage src f₁ x.1.2 := by
        rintro (hzC | hzC)
        · exact Or.inl hzC
        · obtain ⟨t, ht, hzR, hzV⟩ := mem_iUnion₂.mp hzC
          exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, w), ht⟩, rfl, hzR, hzV⟩)
      by_cases hwo : (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
      · by_cases hzC : z ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
            section34CompactSplitDiskImage src f₁ e) ∪
            ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
              Rf t ∩ section34CompactVertexBallImage src f₁ w
        · exact Or.inl (hsplit hzC)
        · have hz' := (hcut.frontier_sdiff_iUnion_eq_of_patch hf₁ Rf w).symm.subset ⟨hz, hzC⟩
          exact Or.inr (mem_iUnion₂.mpr ⟨⟨w, hwo⟩, rfl, subset_closure
            ⟨((hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier).symm.subset hz,
              hz'.2⟩⟩)
      · exact Or.inl (hsplit (hcut.vertexBallImage_frontier_subset_iUnion_residual hf₁ hdisk hR
          hDR hfr hint hio h7 h9 w hwo hz))
    · rintro z ((hz | hz) | hz)
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
        exact hcut.splitDiskImage_subset_frontier hf₁ he hze
      · obtain ⟨x, hxw, hzx⟩ := mem_iUnion₂.mp hz
        have hxw' : Section34Incident w.1 x.1.1.1 := by
          rw [← hxw]
          exact x.2
        rw [hxw] at hzx
        exact residual_inter_vertexBallImage_subset_frontier (hR x.1.1) (hint x.1.1) hxw' hzx
      · obtain ⟨o, how, hzo⟩ := mem_iUnion₂.mp hz
        have hS : IsClosed (section34CompactVertexBallImage srcBd f₁ o.1) := by
          rw [(hcut.isPLCellOn_vertexBallImage hf₁ o.1).boundary_eq_frontier]
          exact isClosed_frontier
        have h := closure_minimal sdiff_subset hS hzo
        rw [how, (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_eq_frontier] at h
        exact h
  · apply Subset.antisymm
    · intro z hz
      by_cases heo : convexHull ℝ (e.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
      · by_cases hzU : z ∈ ⋃ (t : Section34CompactSimplexIndex K 4)
            (_ : Section34Incident e.1 t.1), Rf t ∩ section34CompactSplitDiskImage src f₁ e
        · obtain ⟨t, het, hzR, hzE⟩ := mem_iUnion₂.mp hzU
          exact Or.inl (mem_iUnion₂.mpr ⟨⟨(t, e), het⟩, rfl, hzR, hzE⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨⟨e, heo⟩, rfl, subset_closure
            ((hcut.splitDiskImage_boundary_sdiff_iUnion_eq hf₁ Rf e).symm.subset ⟨hz, hzU⟩)⟩)
      · obtain ⟨t, het, hzR, hzE⟩ := mem_iUnion₂.mp
          (hcut.splitDiskImage_boundary_subset_iUnion_residual hf₁ hdisk hR hDR hfr hint hio h7 h9
            e heo hz)
        exact Or.inl (mem_iUnion₂.mpr ⟨⟨(t, e), het⟩, rfl, hzR, hzE⟩)
    · rintro z (hz | hz)
      · obtain ⟨i, hie, hzi⟩ := mem_iUnion₂.mp hz
        rw [← hie]
        exact hcut.residual_inter_splitDiskImage_subset hf₁ (hR i.1.1) (hint i.1.1) (h7 i.1.1)
          i.1.2 hzi
      · obtain ⟨q, hqe, hzq⟩ := mem_iUnion₂.mp hz
        have hEbc : IsClosed (section34CompactSplitDiskImage srcBd f₁ q.1) :=
          (hcut.isPLCellOn_splitDiskImage hf₁ q.1).isPLSphere_one_of_two.isPolyhedron.isClosed
        have h := closure_minimal sdiff_subset hEbc hzq
        rw [hqe] at h
        exact h

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
