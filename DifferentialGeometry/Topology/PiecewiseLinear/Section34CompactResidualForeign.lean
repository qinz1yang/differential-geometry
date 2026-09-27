/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactCutFrame.vertexBallImage_inter_inter_eq_empty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w₁ w₂ w₃ : Section34CompactVertexIndex K K'} (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃)
    (h₂₃ : w₂ ≠ w₃) :
    section34CompactVertexBallImage src f₁ w₁ ∩ section34CompactVertexBallImage src f₁ w₂ ∩
      section34CompactVertexBallImage src f₁ w₃ = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx
  obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ h₁₂ hx₁ hx₂
  obtain ⟨a, b, -, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hw : ∀ w : Section34CompactVertexIndex K K',
      x ∈ section34CompactVertexBallImage src f₁ w → w = a ∨ w = b := fun w hxw =>
    eq_or_eq_of_section34CompactVertexIndex_subset e habe
      (hcut.subset_of_mem_splitDiskImage hf₁ hxe hxw)
  rcases hw w₁ hx₁ with h1 | h1 <;> rcases hw w₂ hx₂ with h2 | h2 <;>
    rcases hw w₃ hx₃ with h3 | h3
  all_goals first
    | exact h₁₂ (h1.trans h2.symm)
    | exact h₁₃ (h1.trans h3.symm)
    | exact h₂₃ (h2.trans h3.symm)

theorem Section34CompactCutFrame.exists_mem_nhds_frontier_subset_residual
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Section34CompactSimplexIndex K 4} {R W : Set E3} (hR : IsPLBall 3 R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hDc : ∀ s, IsClosed (tgtD s)) (hW : IsPLBall 3 W)
    (hWt : W ⊆ ⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
      section34CompactVertexBallImage src f₁ w)
    {y : E3} (hyR : y ∈ R) (hyW : y ∈ frontier W)
    (hyV : ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 t.1 →
      y ∈ section34CompactVertexBallImage src f₁ w → section34CompactVertexBallImage src f₁ w ⊆ W)
    (hyD : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 → y ∉ tgtD s) :
    ∃ U ∈ 𝓝 y, U ∩ frontier W ⊆ R ∧ U \ W ⊆ interior R := by
  obtain ⟨-, hKfin, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have _ := finite_section34CompactSimplexIndex hKfin 3
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hFc : IsClosed ((⋃ (u : Section34CompactVertexIndex K K')
      (_ : y ∉ section34CompactVertexBallImage src f₁ u),
        section34CompactVertexBallImage src f₁ u) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s) :=
    (isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ => hVc u).union
      (isClosed_iUnion_of_finite fun s => isClosed_iUnion_of_finite fun _ => hDc s)
  refine hW.exists_mem_nhds_of_inter_frontier_subset hR hFc.isOpen_compl ?_
    (hint.mono_right (interior_subset.trans hWt)) ?_ hyR hyW
  · rintro z ⟨hzF, hzR⟩
    rcases hfr hzR with hz | hz
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      by_cases hyu : y ∈ section34CompactVertexBallImage src f₁ u
      · exact hyV u hu hyu hzu
      · exact (hzF (Or.inl (mem_iUnion₂.mpr ⟨u, hyu, hzu⟩))).elim
    · exact (hzF (Or.inr hz)).elim
  · rintro (hy | hy)
    · obtain ⟨u, hu, hyu⟩ := mem_iUnion₂.mp hy
      exact hu hyu
    · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
      exact hyD s hs hys

theorem Section34CompactCutFrame.residual_inter_vertexBallImage_eq_empty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {h : E3 → E3} {fbl : Section34CompactSimplexIndex K 3 → Set E3}
    (hext : Section34CompactExterior K K' h (section34CompactVertexBallImage src f₁) fbl)
    (hDfbl : ∀ s, tgtD s ⊆ fbl s)
    (hcore : ∀ w : Section34CompactVertexIndex K K',
      h '' (w.1 : Set E3) ⊆ interior (section34CompactVertexBallImage src f₁ w))
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    {w' : Section34CompactVertexIndex K K'} (hw' : ¬ Section34Incident w'.1 t.1) :
    R ∩ section34CompactVertexBallImage src f₁ w' = ∅ := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  obtain ⟨hD1, -, -, -, -, -, -, hD8, -⟩ := hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hnot : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      ¬ Section34Incident w'.1 s.1 := fun s hs hws =>
    hw' fun z hz => convexHull_min hs (convex_convexHull ℝ _) (hws hz)
  have hDV : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      ∀ z ∈ section34CompactVertexBallImage src f₁ w', z ∉ tgtD s := by
    intro s hs z hzV hzD
    have h0 : z ∈ tgtD s ∩ section34CompactVertexBallImage src f₁ w' := ⟨hzD, hzV⟩
    rw [hD8 s w' (hnot s hs)] at h0
    exact h0
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w'.2.2.1
  have hpw : p ∈ (w'.1 : Set E3) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hyint : h p ∈ interior (section34CompactVertexBallImage src f₁ w') :=
    hcore w' ⟨p, hpw, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Set E3,
      O = section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t :=
    ⟨_, rfl⟩
  have hfrO : frontier R ⊆ O := by
    rw [hO]
    intro z hz
    rcases hfr hz with hz | hz
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      exact Or.inl (mem_iUnion₂.mpr ⟨⟨(t, u), hu⟩, rfl, hzu⟩)
    · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz
      exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hDfbl s hzs⟩)
  have hunb : ¬ Bornology.IsBounded (connectedComponentIn Oᶜ (h p)) := by
    rw [hO]
    exact hext t w' hw' (h p) ⟨p, hpw, rfl⟩
  have hyO : h p ∈ Oᶜ := by
    intro hyO
    apply hunb
    rw [connectedComponentIn_eq_empty (F := Oᶜ) fun h' => h' hyO]
    exact Bornology.isBounded_empty
  have hyR : h p ∉ R := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hRc
      (isPreconnected_connectedComponentIn (F := Oᶜ) (x := h p))
      (Set.disjoint_left.mpr fun z hz hzR =>
        connectedComponentIn_subset Oᶜ (h p) hz (hfrO hzR)) with hsub | hsub
    · exact absurd (hR.isPolyhedron.isCompact.isBounded.subset
        (hsub.trans interior_subset)) hunb
    · exact hsub (mem_connectedComponentIn hyO)
  have hintV : interior (section34CompactVertexBallImage src f₁ w') ⊆ Rᶜ := by
    have hdisj : Disjoint (interior (section34CompactVertexBallImage src f₁ w'))
        (frontier R) := by
      refine Set.disjoint_left.mpr fun z hz hzR => ?_
      rcases hfr hzR with hz' | hz'
      · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz'
        have hne : w' ≠ u := by
          rintro rfl
          exact hw' hu
        exact Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hne) hz hzu
      · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz'
        exact hDV s hs z (interior_subset hz) hzs
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hRc
      ((hVball w').isConnected_interior_of_finrank hdim).isPreconnected hdisj with hsub | hsub
    · exact absurd (interior_subset (hsub hyint)) hyR
    · exact hsub
  have hRVfr : ∀ z ∈ R, z ∈ section34CompactVertexBallImage src f₁ w' → z ∈ frontier R := by
    intro z hzR hzV
    refine ⟨subset_closure hzR, fun hzi => ?_⟩
    have hzc : z ∈ closure (interior (section34CompactVertexBallImage src f₁ w')) := by
      rw [(hVball w').closure_interior_of_finrank hdim]
      exact hzV
    obtain ⟨q, hqR, hqV⟩ := mem_closure_iff.mp hzc (interior R) isOpen_interior hzi
    exact hintV hqV (interior_subset hqR)
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨hzR, hzV⟩ := hz
  rcases hfr (hRVfr z hzR hzV) with hz' | hz'
  · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz'
    have hne : u ≠ w' := by
      rintro rfl
      exact hw' hu
    have hzfr : z ∈ frontier (section34CompactVertexBallImage src f₁ u) :=
      ⟨subset_closure hzu, fun hzi =>
        Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hne) hzi hzV⟩
    obtain ⟨U, hU, -, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ hR hfr hint hDc
      (hVball u) (subset_iUnion₂_of_subset u hu subset_rfl) hzR hzfr
      (fun v hv hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_rfl
        · have hvw : v ≠ w' := by
            rintro rfl
            exact hw' hv
          have h0 : z ∈ section34CompactVertexBallImage src f₁ v ∩
              section34CompactVertexBallImage src f₁ u ∩
              section34CompactVertexBallImage src f₁ w' := ⟨⟨hzv, hzu⟩, hzV⟩
          rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ hvu hvw hne] at h0
          exact h0.elim)
      (fun s hs => hDV s hs z hzV)
    have hzc : z ∈ closure (interior (section34CompactVertexBallImage src f₁ w')) := by
      rw [(hVball w').closure_interior_of_finrank hdim]
      exact hzV
    obtain ⟨q, hqU, hqV⟩ := mem_closure_iff_nhds.mp hzc U hU
    have hqu : q ∉ section34CompactVertexBallImage src f₁ u := fun hqu =>
      Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hne.symm) hqV hqu
    exact hintV hqV (interior_subset (hUR ⟨hqU, hqu⟩))
  · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz'
    exact hDV s hs z hzV hzs

theorem Section34CompactCutFrame.residual_inter_splitDiskImage_eq_empty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Section34CompactSimplexIndex K 4} {R : Set E3}
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {e : Section34CompactEdgeIndex K K'} (he : ¬ Section34Incident e.1 t.1) :
    R ∩ section34CompactSplitDiskImage src f₁ e = ∅ := by
  obtain ⟨a, b, -, habe, hE⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  rw [hE]
  by_cases ha : Section34Incident a.1 t.1
  · by_cases hb : Section34Incident b.1 t.1
    · refine absurd ?_ he
      change (e.1 : Set E3) ⊆ _
      rw [habe]
      exact union_subset ha hb
    · exact subset_eq_empty (inter_subset_inter_right _ inter_subset_right) (h7 b hb)
  · exact subset_eq_empty (inter_subset_inter_right _ inter_subset_left) (h7 a ha)

theorem Section34CompactCutFrame.exists_mem_nhds_sdiff_iUnion_subset_residual
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hDc : ∀ s, IsClosed (tgtD s))
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {z : E3} (hzR : z ∈ R)
    (hzfr : z ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hzD : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 → z ∉ tgtD s) :
    ∃ U ∈ 𝓝 z, U \ ⋃ w, section34CompactVertexBallImage src f₁ w ⊆ interior R := by
  obtain ⟨-, -, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hUc : IsClosed (⋃ w, section34CompactVertexBallImage src f₁ w) :=
    isClosed_iUnion_of_finite fun u => (hVball u).isPolyhedron.isClosed
  have hinc : ∀ u, z ∈ section34CompactVertexBallImage src f₁ u → Section34Incident u.1 t.1 := by
    intro u hzu
    by_contra hu
    have h0 : z ∈ R ∩ section34CompactVertexBallImage src f₁ u := ⟨hzR, hzu⟩
    rw [h7 u hu] at h0
    exact h0
  have hfrW : ∀ {W : Set E3}, W ⊆ ⋃ w, section34CompactVertexBallImage src f₁ w → z ∈ W →
      z ∈ frontier W := fun hW hzW => ⟨subset_closure hzW, fun hzi => hzfr.2 (interior_mono hW hzi)⟩
  obtain ⟨u, hzu⟩ := mem_iUnion.mp (hUc.frontier_subset hzfr)
  have hu := hinc u hzu
  by_cases h2 : ∃ u', u' ≠ u ∧ z ∈ section34CompactVertexBallImage src f₁ u'
  · obtain ⟨u', hu'u, hzu'⟩ := h2
    have hu' := hinc u' hzu'
    obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hu'u.symm hzu hzu'
    have hue := hcut.subset_of_mem_splitDiskImage hf₁ hze hzu
    have hu'e := hcut.subset_of_mem_splitDiskImage hf₁ hze hzu'
    have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hu'u.symm hue hu'e
    obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
    have hWball : IsPLBall 3 (section34CompactVertexBallImage src f₁ u ∪
        section34CompactVertexBallImage src f₁ u') :=
      isPLBall_union_of_inter_eq_of_subset_frontier (hVball u) (hVball u') ⟨q, hq⟩ hinter
        (hcut.splitDiskImage_subset_frontier hf₁ hu'e)
    have hWU : section34CompactVertexBallImage src f₁ u ∪
        section34CompactVertexBallImage src f₁ u' ⊆ ⋃ w, section34CompactVertexBallImage src f₁ w :=
      union_subset (subset_iUnion _ u) (subset_iUnion _ u')
    obtain ⟨U, hU, -, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ hR hfr hint hDc
      hWball (union_subset (subset_iUnion₂_of_subset u hu subset_rfl)
        (subset_iUnion₂_of_subset u' hu' subset_rfl)) hzR (hfrW hWU (Or.inl hzu))
      (fun v _ hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_union_left
        · by_cases hvu' : v = u'
          · subst hvu'
            exact subset_union_right
          · have h0 : z ∈ section34CompactVertexBallImage src f₁ v ∩
                section34CompactVertexBallImage src f₁ u ∩
                section34CompactVertexBallImage src f₁ u' := ⟨⟨hzv, hzu⟩, hzu'⟩
            rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ hvu hvu' hu'u.symm] at h0
            exact h0.elim)
      hzD
    exact ⟨U, hU, fun y hy => hUR ⟨hy.1, fun hyW => hy.2 (hWU hyW)⟩⟩
  · obtain ⟨U, hU, -, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ hR hfr hint hDc
      (hVball u) (subset_iUnion₂_of_subset u hu subset_rfl) hzR (hfrW (subset_iUnion _ u) hzu)
      (fun v _ hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_rfl
        · exact absurd ⟨v, hvu, hzv⟩ h2)
      hzD
    exact ⟨U, hU, fun y hy => hUR ⟨hy.1, fun hyW => hy.2 (subset_iUnion _ u hyW)⟩⟩

theorem Section34CompactCutFrame.residual_inter_faceDisk_eq_empty
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {s : Section34CompactSimplexIndex K 3} (hs : ¬ Section34Incident s.1 t.1) :
    R ∩ tgtD s = ∅ := by
  classical
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  obtain ⟨hD1, -, hD3, hD4, hD5, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  obtain ⟨x, hxs, hxt⟩ := not_subset.mp hs
  obtain ⟨y, hys, hyx⟩ := Finset.exists_mem_ne (by rw [s.2.2]; norm_num) x
  have hxyK : ({x, y} : Finset E3) ∈ K.faces :=
    K.down_closed s.2.1 (Finset.insert_subset hxs (Finset.singleton_subset_iff.mpr hys))
      (Finset.insert_nonempty x {y})
  obtain ⟨n, w, e, hn, hw0, -⟩ := hcut.exists_vertexIndex_path hyx.symm hxyK
  have hw0s : Section34Incident (w 0).1 s.1 := by
    change ((w 0).1 : Set E3) ⊆ _
    rw [hw0, Finset.coe_singleton, singleton_subset_iff]
    exact subset_convexHull ℝ _ hxs
  have hw0t : ¬ Section34Incident (w 0).1 t.1 := by
    change ¬ ((w 0).1 : Set E3) ⊆ _
    rw [hw0, Finset.coe_singleton, singleton_subset_iff]
    exact hxt
  obtain ⟨z₀, hz₀⟩ := (hdisk.2.2.2.2.2.1 ⟨(s, w 0), hw0s⟩).nonempty
  rw [← hdisk.faceDisk_inter_vertexBallImage_eq ⟨(s, w 0), hw0s⟩] at hz₀
  have hz₀R : z₀ ∉ R := fun hz₀R => by
    have h0 : z₀ ∈ R ∩ section34CompactVertexBallImage src f₁ (w 0) := ⟨hz₀R, hz₀.2⟩
    rw [h7 (w 0) hw0t] at h0
    exact h0
  obtain ⟨q, hq, hqb⟩ := (hD1 s).exists_isPLHomeomorphOn_stdSimplex
  have hconn : IsConnected (tgtD s \ tgtDBd s) := by
    rw [hqb]
    exact hq.isConnected_sdiff_image_stdSimplexBoundary (n := 1)
  have hcl : closure (tgtD s \ tgtDBd s) = tgtD s := by
    rw [hqb]
    exact hq.closure_sdiff_image_stdSimplexBoundary (n := 1)
  have hDsV : ∀ z ∈ tgtD s \ tgtDBd s, z ∉ ⋃ w, section34CompactVertexBallImage src f₁ w :=
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
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hRc hconn.isPreconnected hdisj
      with hsub | hsub
    · refine absurd ?_ hz₀R
      have h := closure_mono (hsub.trans interior_subset) (hcl.symm.subset hz₀.1)
      rwa [hRc.closure_eq] at h
    · exact hsub
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨hzR, hzD⟩ := hz
  by_cases hzb : z ∈ tgtDBd s
  · obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_sdiff_iUnion_subset_residual hf₁ hR hfr hint hDc
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
