/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualForeignFace

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
theorem Section34FaceDiskFamily.interior_residual_inter_residual_eq_empty
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34SimplexIndex 𝒦 4 → Set M₂} (hR : ∀ t, IsPLCellOn 3 (Rf t) (frontier (Rf t)))
    (hDR : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34SimplexIndex 𝒦 4, frontier (Rf t) ⊆
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34SimplexIndex 𝒦 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w))
    (h7 : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34VertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {t t' : Section34SimplexIndex 𝒦 4} (htt : t ≠ t') :
    interior (Rf t') ∩ Rf t = ∅ := by
  classical
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
  have hxyz : ({x, y, z} : Finset Ea) ⊆ t'.1 := Finset.insert_subset hxt'
    (Finset.insert_subset (Finset.mem_of_mem_erase hy)
      (Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hz)))
  let s : Section34SimplexIndex 𝒦 3 :=
    ⟨{x, y, z}, 𝒦.complex.down_closed t'.2.1 hxyz (Finset.insert_nonempty _ _),
      Finset.card_eq_three.mpr ⟨x, y, z, (Finset.ne_of_mem_erase hy).symm,
        (Finset.ne_of_mem_erase hz).symm, hyz, rfl⟩⟩
  have hs' : Section34Incident s.1 t'.1 := fun q hq => subset_convexHull ℝ _ (hxyz hq)
  have hs : ¬ Section34Incident s.1 t.1 :=
    SimplicialComplex.not_section34Incident_of_notMem_left t.2.1
      (𝒦.complex.down_closed t'.2.1 (Finset.singleton_subset_iff.mpr hxt')
        (Finset.singleton_nonempty x))
      (Finset.mem_insert_self x _) hxt
  have hdisj : Disjoint (interior (Rf t')) (frontier (Rf t)) := by
    refine Set.disjoint_left.mpr fun q hq hqR => ?_
    rcases hfr t hqR with hq' | hq'
    · obtain ⟨w, -, hqw⟩ := mem_iUnion₂.mp hq'
      by_cases hw' : Section34Incident w.1 t'.1
      · exact Set.disjoint_left.mp (hint t') hq (mem_iUnion₂.mpr ⟨w, hw', hqw⟩)
      · have h0 : q ∈ Rf t' ∩ section34VertexBallImage src f₁ w :=
          ⟨interior_subset hq, hqw⟩
        rw [h7 t' w hw'] at h0
        exact h0
    · obtain ⟨s', -, hqs'⟩ := mem_iUnion₂.mp hq'
      by_cases hs'' : Section34Incident s'.1 t'.1
      · exact Set.disjoint_left.mp disjoint_interior_frontier hq (hDR t' s' hs'' hqs')
      · have h0 : q ∈ Rf t' ∩ tgtD s' := ⟨interior_subset hq, hqs'⟩
        rw [h9 t' s' hs''] at h0
        exact h0
  have hconn : IsConnected (interior (Rf t')) :=
    (hR t').isConnected_of_sdiff_subset
      (by rw [(hR t').sdiff_boundary_eq_interior]) interior_subset
  rcases DifferentialGeometry.Topology.subset_interior_or_subset_compl_of_disjoint_frontier
    (hR t).isCompact.isClosed hconn.isPreconnected hdisj with hsub' | hsub'
  · exfalso
    obtain ⟨q, hq⟩ := (hD1 s).nonempty
    have hqR' : q ∈ Rf t' := (hR t').isCompact.isClosed.frontier_subset (hDR t' s hs' hq)
    have hqcl := (hR t').subset_closure_interior hqR'
    have hqR : q ∈ Rf t :=
      closure_minimal (hsub'.trans interior_subset) (hR t).isCompact.isClosed hqcl
    have h0 : q ∈ Rf t ∩ tgtD s := ⟨hqR, hq⟩
    rw [h9 t s hs] at h0
    exact h0
  · exact eq_empty_iff_forall_notMem.mpr fun q hq => hsub' hq.1 hq.2

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.residual_inter_residual_subset
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34SimplexIndex 𝒦 4 → Set M₂} (hR : ∀ t, IsPLCellOn 3 (Rf t) (frontier (Rf t)))
    (hDR : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34SimplexIndex 𝒦 4, frontier (Rf t) ⊆
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34SimplexIndex 𝒦 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w))
    (h7 : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34VertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {t t' : Section34SimplexIndex 𝒦 4} (htt : t ≠ t') :
    Rf t ∩ Rf t' ⊆ ⋃ s, tgtD s := by
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hb := hdisk.interior_residual_inter_residual_eq_empty hR hDR hfr hint h7 h9 htt
  have hb' := hdisk.interior_residual_inter_residual_eq_empty hR hDR hfr hint h7 h9 htt.symm
  intro y hy
  by_contra hyD
  have hyD' : ∀ s : Section34SimplexIndex 𝒦 3, y ∉ tgtD s := fun s hys =>
    hyD (mem_iUnion.mpr ⟨s, hys⟩)
  have hyi : y ∉ interior (Rf t) := fun hyi => by
    have h0 : y ∈ interior (Rf t) ∩ Rf t' := ⟨hyi, hy.2⟩
    rw [hb'] at h0
    exact h0
  have hyfr : y ∈ frontier (⋃ w, section34VertexBallImage src f₁ w) := by
    rcases hfr t ⟨subset_closure hy.1, hyi⟩ with hyV | hyV'
    · obtain ⟨w, -, hyw⟩ := mem_iUnion₂.mp hyV
      refine ⟨subset_closure (mem_iUnion.mpr ⟨w, hyw⟩), fun hyint => ?_⟩
      have hyc := (hR t).subset_closure_interior hy.1
      obtain ⟨q, hqV, hqR⟩ := mem_closure_iff.mp hyc _ isOpen_interior hyint
      obtain ⟨u, hqu⟩ := mem_iUnion.mp (interior_subset hqV)
      by_cases hu : Section34Incident u.1 t.1
      · exact Set.disjoint_left.mp (hint t) hqR (mem_iUnion₂.mpr ⟨u, hu, hqu⟩)
      · have h0 : q ∈ Rf t ∩ section34VertexBallImage src f₁ u :=
          ⟨interior_subset hqR, hqu⟩
        rw [h7 t u hu] at h0
        exact h0
    · obtain ⟨s, -, hys⟩ := mem_iUnion₂.mp hyV'
      exact absurd hys (hyD' s)
  obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_sdiff_iUnion_subset_residual (hR t) (hfr t)
    (hint t) hDc (h7 t) hy.1 hyfr fun s _ => hyD' s
  obtain ⟨U', hU', hUR'⟩ := hdata.exists_mem_nhds_sdiff_iUnion_subset_residual (hR t')
    (hfr t') (hint t') hDc (h7 t') hy.2 hyfr fun s _ => hyD' s
  have hyc : y ∈ closure (⋃ w, section34VertexBallImage src f₁ w)ᶜ := by
    rw [closure_compl]
    exact hyfr.2
  obtain ⟨q, ⟨hqU, hqU'⟩, hqV⟩ := mem_closure_iff_nhds.mp hyc (U ∩ U') (Filter.inter_mem hU hU')
  have h0 : q ∈ interior (Rf t') ∩ Rf t :=
    ⟨hUR' ⟨hqU', hqV⟩, interior_subset (hUR ⟨hqU, hqV⟩)⟩
  rw [hb] at h0
  exact h0

end DifferentialGeometry.Topology.PiecewiseLinear
