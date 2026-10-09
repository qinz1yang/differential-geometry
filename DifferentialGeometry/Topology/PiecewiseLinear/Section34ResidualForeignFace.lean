/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualForeignVertex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.exists_mem_nhds_sdiff_iUnion_subset_residual
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hDc : ∀ s, IsClosed (tgtD s))
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {z : M₂} (hzR : z ∈ R)
    (hzfr : z ∈ frontier (⋃ w, section34VertexBallImage src f₁ w))
    (hzD : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 → z ∉ tgtD s) :
    ∃ U ∈ 𝓝 z, U \ ⋃ w, section34VertexBallImage src f₁ w ⊆ interior R := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hintAll : Disjoint (interior R) (⋃ w, section34VertexBallImage src f₁ w) := by
    refine Set.disjoint_left.mpr fun y hy hyV => ?_
    obtain ⟨w, hyw⟩ := mem_iUnion.mp hyV
    by_cases hw : Section34Incident w.1 t.1
    · exact Set.disjoint_left.mp hint hy (mem_iUnion₂.mpr ⟨w, hw, hyw⟩)
    · have hm : y ∈ R ∩ section34VertexBallImage src f₁ w := ⟨interior_subset hy, hyw⟩
      rw [h7 w hw] at hm
      exact hm
  have hzRf : z ∈ frontier R := by
    refine ⟨subset_closure hzR, fun hzi => ?_⟩
    obtain ⟨y, hyR, hyV⟩ := mem_closure_iff.mp hzfr.1 (interior R) isOpen_interior hzi
    exact Set.disjoint_left.mp hintAll hyR hyV
  have hzmem : ∃ u, z ∈ section34VertexBallImage src f₁ u := by
    rcases hfr hzRf with hzV | hzD'
    · obtain ⟨u, -, hzu⟩ := mem_iUnion₂.mp hzV
      exact ⟨u, hzu⟩
    · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hzD'
      exact (hzD s hs hzs).elim
  have hinc : ∀ u, z ∈ section34VertexBallImage src f₁ u → Section34Incident u.1 t.1 := by
    intro u hzu
    by_contra hu
    have h0 : z ∈ R ∩ section34VertexBallImage src f₁ u := ⟨hzR, hzu⟩
    rw [h7 u hu] at h0
    exact h0
  have hfrW : ∀ {W : Set M₂}, W ⊆ ⋃ w, section34VertexBallImage src f₁ w → z ∈ W →
      z ∈ frontier W := fun hW hzW => ⟨subset_closure hzW, fun hzi => hzfr.2 (interior_mono hW hzi)⟩
  obtain ⟨u, hzu⟩ := hzmem
  have hu := hinc u hzu
  by_cases h2 : ∃ u', u' ≠ u ∧ z ∈ section34VertexBallImage src f₁ u'
  · obtain ⟨u', hu'u, hzu'⟩ := h2
    have hu' := hinc u' hzu'
    obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hu'u.symm hzu hzu'
    have hue := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzu
    have hu'e := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzu'
    have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hu'u.symm hue hu'e
    obtain ⟨chart, hchart, -, hVsrc, -⟩ := hdata.exists_chart_tetrahedron t
    have hWball : IsPLCellOn 3 (section34VertexBallImage src f₁ u ∪
        section34VertexBallImage src f₁ u')
        (frontier (section34VertexBallImage src f₁ u ∪ section34VertexBallImage src f₁ u')) :=
      (hVball u).union_of_inter_eq_of_subset_frontier_in_chart (hVball u')
        (hcut.isPLCellOn_splitDiskImage hf₁ e) hinter
        (hcut.splitDiskImage_subset_frontier hf₁ hu'e) hchart (hVsrc u hu) (hVsrc u' hu')
    have hWU : section34VertexBallImage src f₁ u ∪
        section34VertexBallImage src f₁ u' ⊆ ⋃ w, section34VertexBallImage src f₁ w :=
      union_subset (subset_iUnion _ u) (subset_iUnion _ u')
    obtain ⟨U, hU, -, hUR⟩ := hdata.exists_mem_nhds_frontier_subset_residual hR hfr hint hDc
      hWball (union_subset (subset_iUnion₂_of_subset u hu subset_rfl)
        (subset_iUnion₂_of_subset u' hu' subset_rfl)) hzR (hfrW hWU (Or.inl hzu))
      (fun v _ hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_union_left
        · by_cases hvu' : v = u'
          · subst hvu'
            exact subset_union_right
          · have h0 : z ∈ section34VertexBallImage src f₁ v ∩
                section34VertexBallImage src f₁ u ∩
                section34VertexBallImage src f₁ u' := ⟨⟨hzv, hzu⟩, hzu'⟩
            rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁.injOn hvu hvu' hu'u.symm] at h0
            exact h0.elim)
      hzD
    exact ⟨U, hU, fun y hy => hUR ⟨hy.1, fun hyW => hy.2 (hWU hyW)⟩⟩
  · obtain ⟨U, hU, -, hUR⟩ := hdata.exists_mem_nhds_frontier_subset_residual hR hfr hint hDc
      (hVball u) (subset_iUnion₂_of_subset u hu subset_rfl) hzR (hfrW (subset_iUnion _ u) hzu)
      (fun v _ hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_rfl
        · exact absurd ⟨v, hvu, hzv⟩ h2)
      hzD
    exact ⟨U, hU, fun y hy => hUR ⟨hy.1, fun hyW => hy.2 (subset_iUnion _ u hyW)⟩⟩

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.residual_inter_faceDisk_eq_empty
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {s : Section34SimplexIndex 𝒦 3} (hs : ¬ Section34Incident s.1 t.1) :
    R ∩ tgtD s = ∅ := by
  classical
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hRc : IsClosed R := hR.isCompact.isClosed
  obtain ⟨hD1, -, hD3, hD4, hD5, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  obtain ⟨x, hxs, hxt⟩ := not_subset.mp hs
  obtain ⟨y, hys, hyx⟩ := Finset.exists_mem_ne (by rw [s.2.2]; norm_num) x
  have hxyK : ({x, y} : Finset Ea) ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed s.2.1 (Finset.insert_subset hxs (Finset.singleton_subset_iff.mpr hys))
      (Finset.insert_nonempty x {y})
  obtain ⟨n, w, e, hn, hw0, -⟩ := hcut.exists_vertexIndex_path hyx.symm hxyK
  have hw0s : Section34Incident (w 0).1 s.1 := by
    change ((w 0).1 : Set Ea) ⊆ _
    rw [hw0, Finset.coe_singleton, singleton_subset_iff]
    exact subset_convexHull ℝ _ hxs
  have hw0t : ¬ Section34Incident (w 0).1 t.1 := by
    change ¬ ((w 0).1 : Set Ea) ⊆ _
    rw [hw0, Finset.coe_singleton, singleton_subset_iff]
    exact hxt
  obtain ⟨z₀, hz₀⟩ := (hdisk.2.2.2.2.2.1 ⟨(s, w 0), hw0s⟩).nonempty
  rw [← hdisk.faceDisk_inter_vertexBall_eq ⟨(s, w 0), hw0s⟩] at hz₀
  have hz₀R : z₀ ∉ R := fun hz₀R => by
    have h0 : z₀ ∈ R ∩ section34VertexBallImage src f₁ (w 0) := ⟨hz₀R, hz₀.2⟩
    rw [h7 (w 0) hw0t] at h0
    exact h0
  have hconn : IsConnected (tgtD s \ tgtDBd s) :=
    (hD1 s).isConnected_of_sdiff_subset subset_rfl sdiff_subset
  have hcl : closure (tgtD s \ tgtDBd s) = tgtD s := (hD1 s).closure_sdiff_boundary
  have hDsV : ∀ z ∈ tgtD s \ tgtDBd s, z ∉ ⋃ w, section34VertexBallImage src f₁ w :=
    fun z hz hzV => hz.2 (by rw [← hD3 s]; exact ⟨hz.1, hzV⟩)
  have hdisj : Disjoint (tgtD s \ tgtDBd s) (frontier R) := by
    refine Set.disjoint_left.mpr fun z hz hzR => ?_
    rcases hfr hzR with hz' | hz'
    · obtain ⟨u, -, hzu⟩ := mem_iUnion₂.mp hz'
      exact hDsV z hz (mem_iUnion.mpr ⟨u, hzu⟩)
    · obtain ⟨s', hs', hzs'⟩ := mem_iUnion₂.mp hz'
      have hne : s ≠ s' := by
        rintro rfl
        exact hs hs'
      exact Set.disjoint_left.mp (hD5 s s' hne) hz.1 hzs'
  have hout : tgtD s \ tgtDBd s ⊆ Rᶜ := by
    rcases DifferentialGeometry.Topology.subset_interior_or_subset_compl_of_disjoint_frontier
      hRc hconn.isPreconnected hdisj
      with hsub | hsub
    · refine absurd ?_ hz₀R
      have h := closure_mono (hsub.trans interior_subset) (hcl.symm.subset hz₀.1)
      rwa [hRc.closure_eq] at h
    · exact hsub
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨hzR, hzD⟩ := hz
  by_cases hzb : z ∈ tgtDBd s
  · obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_sdiff_iUnion_subset_residual hR hfr hint hDc
      h7 hzR (hD4 s hzb) (fun s' hs' hzs' => by
        have hne : s ≠ s' := by
          rintro rfl
          exact hs hs'
        exact Set.disjoint_left.mp (hD5 s s' hne) hzD hzs')
    have hzc : z ∈ closure (tgtD s \ tgtDBd s) := by
      rw [hcl]
      exact hzD
    obtain ⟨q', hq'U, hq'D⟩ := mem_closure_iff_nhds.mp hzc U hU
    exact hout hq'D (interior_subset (hUR ⟨hq'U, hDsV q' hq'D⟩))
  · exact hout ⟨hzD, hzb⟩ hzR
end DifferentialGeometry.Topology.PiecewiseLinear
