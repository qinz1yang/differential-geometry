/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPatchCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem interior_residual_inter_residual_eq_empty
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {t t' : Section34CompactSimplexIndex K 4} (htt : t ≠ t') :
    interior (Rf t') ∩ Rf t = ∅ := by
  classical
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  obtain ⟨hD1, -⟩ := id hdisk
  have hsub : ¬ t'.1 ⊆ t.1 := fun h => htt (Subtype.ext
    (Finset.eq_of_subset_of_card_le h (le_of_eq (by rw [t.2.2, t'.2.2]))).symm)
  obtain ⟨x, hxt', hxt⟩ := Finset.not_subset.mp hsub
  have hcard : (t'.1.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxt', t'.2.2]
  obtain ⟨y, z, u, hyz, -, -, hyzu⟩ := Finset.card_eq_three.mp hcard
  have hy : y ∈ t'.1.erase x := by
    rw [hyzu]
    simp
  have hz : z ∈ t'.1.erase x := by
    rw [hyzu]
    simp
  have hxyz : ({x, y, z} : Finset E3) ⊆ t'.1 := Finset.insert_subset hxt'
    (Finset.insert_subset (Finset.mem_of_mem_erase hy)
      (Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hz)))
  let s : Section34CompactSimplexIndex K 3 :=
    ⟨{x, y, z}, K.down_closed t'.2.1 hxyz (Finset.insert_nonempty _ _),
      Finset.card_eq_three.mpr ⟨x, y, z, (Finset.ne_of_mem_erase hy).symm,
        (Finset.ne_of_mem_erase hz).symm, hyz, rfl⟩⟩
  have hs' : Section34Incident s.1 t'.1 := fun q hq => subset_convexHull ℝ _ (hxyz hq)
  have hs : ¬ Section34Incident s.1 t.1 :=
    not_section34Incident_of_notMem_left t.2.1
      (K.down_closed t'.2.1 (Finset.singleton_subset_iff.mpr hxt') (Finset.singleton_nonempty x))
      (Finset.mem_insert_self x _) hxt
  have hdisj : Disjoint (interior (Rf t')) (frontier (Rf t)) := by
    refine Set.disjoint_left.mpr fun q hq hqR => ?_
    rcases hfr t hqR with hq' | hq'
    · obtain ⟨w, -, hqw⟩ := mem_iUnion₂.mp hq'
      by_cases hw' : Section34Incident w.1 t'.1
      · exact Set.disjoint_left.mp (hint t') hq (mem_iUnion₂.mpr ⟨w, hw', hqw⟩)
      · have h0 : q ∈ Rf t' ∩ section34CompactVertexBallImage src f₁ w :=
          ⟨interior_subset hq, hqw⟩
        rw [h7 t' w hw'] at h0
        exact h0
    · obtain ⟨s', -, hqs'⟩ := mem_iUnion₂.mp hq'
      by_cases hs'' : Section34Incident s'.1 t'.1
      · exact Set.disjoint_left.mp disjoint_interior_frontier hq (hDR t' s' hs'' hqs')
      · have h0 : q ∈ Rf t' ∩ tgtD s' := ⟨interior_subset hq, hqs'⟩
        rw [h9 t' s' hs''] at h0
        exact h0
  rcases subset_interior_or_subset_compl_of_disjoint_frontier (hR t).isPolyhedron.isClosed
    ((hR t').isConnected_interior_of_finrank hdim).isPreconnected hdisj with hsub' | hsub'
  · exfalso
    obtain ⟨q, hq⟩ := (hD1 s).nonempty
    have hqR' : q ∈ Rf t' := (hR t').isPolyhedron.isClosed.frontier_subset (hDR t' s hs' hq)
    rw [← (hR t').closure_interior_of_finrank hdim] at hqR'
    have hqR : q ∈ Rf t :=
      closure_minimal (hsub'.trans interior_subset) (hR t).isPolyhedron.isClosed hqR'
    have h0 : q ∈ Rf t ∩ tgtD s := ⟨hqR, hq⟩
    rw [h9 t s hs] at h0
    exact h0
  · exact eq_empty_iff_forall_notMem.mpr fun q hq => hsub' hq.1 hq.2

theorem Section34CompactCutFrame.residual_inter_residual_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {t t' : Section34CompactSimplexIndex K 4} (htt : t ≠ t') :
    Rf t ∩ Rf t' ⊆ ⋃ s, tgtD s := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hb := interior_residual_inter_residual_eq_empty hdisk hR hDR hfr hint h7 h9 htt
  have hb' := interior_residual_inter_residual_eq_empty hdisk hR hDR hfr hint h7 h9 htt.symm
  intro y hy
  by_contra hyD
  have hyD' : ∀ s : Section34CompactSimplexIndex K 3, y ∉ tgtD s := fun s hys =>
    hyD (mem_iUnion.mpr ⟨s, hys⟩)
  have hyi : y ∉ interior (Rf t) := fun hyi => by
    have h0 : y ∈ interior (Rf t) ∩ Rf t' := ⟨hyi, hy.2⟩
    rw [hb'] at h0
    exact h0
  have hyfr : y ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    rcases hfr t ⟨subset_closure hy.1, hyi⟩ with hyV | hyV'
    · obtain ⟨w, -, hyw⟩ := mem_iUnion₂.mp hyV
      refine ⟨subset_closure (mem_iUnion.mpr ⟨w, hyw⟩), fun hyint => ?_⟩
      have hyc : y ∈ closure (interior (Rf t)) := by
        rw [(hR t).closure_interior_of_finrank hdim]
        exact hy.1
      obtain ⟨q, hqV, hqR⟩ := mem_closure_iff.mp hyc _ isOpen_interior hyint
      obtain ⟨u, hqu⟩ := mem_iUnion.mp (interior_subset hqV)
      by_cases hu : Section34Incident u.1 t.1
      · exact Set.disjoint_left.mp (hint t) hqR (mem_iUnion₂.mpr ⟨u, hu, hqu⟩)
      · have h0 : q ∈ Rf t ∩ section34CompactVertexBallImage src f₁ u :=
          ⟨interior_subset hqR, hqu⟩
        rw [h7 t u hu] at h0
        exact h0
    · obtain ⟨s, -, hys⟩ := mem_iUnion₂.mp hyV'
      exact absurd hys (hyD' s)
  obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_sdiff_iUnion_subset_residual hf₁ (hR t) (hfr t)
    (hint t) hDc (h7 t) hy.1 hyfr fun s _ => hyD' s
  obtain ⟨U', hU', hUR'⟩ := hcut.exists_mem_nhds_sdiff_iUnion_subset_residual hf₁ (hR t')
    (hfr t') (hint t') hDc (h7 t') hy.2 hyfr fun s _ => hyD' s
  have hyc : y ∈ closure (⋃ w, section34CompactVertexBallImage src f₁ w)ᶜ := by
    rw [closure_compl]
    exact hyfr.2
  obtain ⟨q, ⟨hqU, hqU'⟩, hqV⟩ := mem_closure_iff_nhds.mp hyc (U ∩ U') (Filter.inter_mem hU hU')
  have h0 : q ∈ interior (Rf t') ∩ Rf t :=
    ⟨hUR' ⟨hqU', hqV⟩, interior_subset (hUR ⟨hqU, hqV⟩)⟩
  rw [hb] at h0
  exact h0

theorem Section34CompactCutFrame.exists_mem_nhds_frontier_subset_union
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {t₁ t₂ : Section34CompactSimplexIndex K 4} (ht : t₁ ≠ t₂)
    {s : Section34CompactSimplexIndex K 3} (hs₁ : Section34Incident s.1 t₁.1)
    (hs₂ : Section34Incident s.1 t₂.1) {W : Set E3}
    (hWt : W ⊆ ⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t₂.1),
      section34CompactVertexBallImage src f₁ w)
    (hRW : IsPLBall 3 (Rf t₁ ∪ W)) {z : E3} (hzD : z ∈ tgtD s)
    (hzV : ∀ w, z ∈ section34CompactVertexBallImage src f₁ w →
      section34CompactVertexBallImage src f₁ w ⊆ W) :
    ∃ U ∈ 𝓝 z, U ∩ frontier W ⊆ Rf t₁ ∪ Rf t₂ := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  obtain ⟨-, hKfin, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have _ := finite_section34CompactSimplexIndex hKfin 3
  obtain ⟨hD1, -, -, -, hD5, -⟩ := id hdisk
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hR₁c : IsClosed (Rf t₁) := (hR t₁).isPolyhedron.isClosed
  have hR₂c : IsClosed (Rf t₂) := (hR t₂).isPolyhedron.isClosed
  have hb := interior_residual_inter_residual_eq_empty hdisk hR hDR hfr hint h7 h9 ht
  have hFc : IsClosed ((⋃ (u : Section34CompactVertexIndex K K')
      (_ : z ∉ section34CompactVertexBallImage src f₁ u),
        section34CompactVertexBallImage src f₁ u) ∪
      ⋃ (s' : Section34CompactSimplexIndex K 3) (_ : z ∉ tgtD s'), tgtD s') :=
    (isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ => hVc u).union
      (isClosed_iUnion_of_finite fun s' => isClosed_iUnion_of_finite fun _ => hDc s')
  have hzF : z ∉ (⋃ (u : Section34CompactVertexIndex K K')
      (_ : z ∉ section34CompactVertexBallImage src f₁ u),
        section34CompactVertexBallImage src f₁ u) ∪
      ⋃ (s' : Section34CompactSimplexIndex K 3) (_ : z ∉ tgtD s'), tgtD s' := by
    rintro (hz | hz)
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      exact hu hzu
    · obtain ⟨s', hs', hzs'⟩ := mem_iUnion₂.mp hz
      exact hs' hzs'
  have hDsub : tgtD s ⊆ Rf t₁ := fun q hq => hR₁c.frontier_subset (hDR t₁ s hs₁ hq)
  have hRO : ((⋃ (u : Section34CompactVertexIndex K K')
      (_ : z ∉ section34CompactVertexBallImage src f₁ u),
        section34CompactVertexBallImage src f₁ u) ∪
      ⋃ (s' : Section34CompactSimplexIndex K 3) (_ : z ∉ tgtD s'), tgtD s')ᶜ ∩
        frontier (Rf t₂) ⊆ Rf t₁ ∪ W := by
    rintro q ⟨hqF, hqR⟩
    rcases hfr t₂ hqR with hq | hq
    · obtain ⟨u, -, hqu⟩ := mem_iUnion₂.mp hq
      by_cases hzu : z ∈ section34CompactVertexBallImage src f₁ u
      · exact Or.inr (hzV u hzu hqu)
      · exact (hqF (Or.inl (mem_iUnion₂.mpr ⟨u, hzu, hqu⟩))).elim
    · obtain ⟨s', -, hqs'⟩ := mem_iUnion₂.mp hq
      by_cases hzs' : z ∈ tgtD s'
      · have hss : s' = s := by
          by_contra hne
          exact Set.disjoint_left.mp (hD5 s' s hne) hzs' hzD
        rw [hss] at hqs'
        exact Or.inl (hDsub hqs')
      · exact (hqF (Or.inr (mem_iUnion₂.mpr ⟨s', hzs', hqs'⟩))).elim
  have hintd : Disjoint (interior (Rf t₂)) (interior (Rf t₁ ∪ W)) := by
    refine Set.disjoint_left.mpr fun q hq hq' => ?_
    rcases interior_subset hq' with hq1 | hqW
    · have h0 : q ∈ interior (Rf t₂) ∩ Rf t₁ := ⟨hq, hq1⟩
      rw [hb] at h0
      exact h0
    · exact Set.disjoint_left.mp (hint t₂) hq (hWt hqW)
  have hz₂ : z ∈ Rf t₂ := hR₂c.frontier_subset (hDR t₂ s hs₂ hzD)
  have hzfr : z ∈ frontier (Rf t₁ ∪ W) := by
    refine ⟨subset_closure (Or.inl (hDsub hzD)), fun hzi => ?_⟩
    have hzc : z ∈ closure (interior (Rf t₂)) := by
      rw [(hR t₂).closure_interior_of_finrank hdim]
      exact hz₂
    obtain ⟨q, hq, hq'⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
    exact Set.disjoint_left.mp hintd hq' hq
  obtain ⟨U, hU, -, hUR⟩ := hRW.exists_mem_nhds_of_inter_frontier_subset (hR t₂)
    hFc.isOpen_compl hRO hintd hzF hz₂ hzfr
  refine ⟨interior U, interior_mem_nhds.mpr hU, fun q hq => ?_⟩
  have hqc : q ∈ closure Wᶜ := by
    rw [closure_compl]
    exact hq.2.2
  have hsub : interior U ∩ Wᶜ ⊆ Rf t₁ ∪ Rf t₂ := fun q' hq' => by
    by_cases h1 : q' ∈ Rf t₁
    · exact Or.inl h1
    · exact Or.inr (interior_subset (hUR ⟨interior_subset hq'.1, fun h => h.elim h1 hq'.2⟩))
  have h := closure_mono hsub (isOpen_interior.inter_closure ⟨hq.1, hqc⟩)
  rwa [(hR₁c.union hR₂c).closure_eq] at h

end DifferentialGeometry.Topology.PiecewiseLinear
