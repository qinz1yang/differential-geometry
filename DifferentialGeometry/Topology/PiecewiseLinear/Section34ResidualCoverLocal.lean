/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualPairs

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
theorem Section34NormalPlus.exists_mem_nhds_frontier_subset_union
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
    {t₁ t₂ : Section34SimplexIndex 𝒦 4} (ht : t₁ ≠ t₂)
    {s : Section34SimplexIndex 𝒦 3} (hs₁ : Section34Incident s.1 t₁.1)
    (hs₂ : Section34Incident s.1 t₂.1) {W : Set M₂}
    (hWt : W ⊆ ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t₂.1),
      section34VertexBallImage src f₁ w)
    (hRW : IsPLCellOn 3 (Rf t₁ ∪ W) (frontier (Rf t₁ ∪ W)))
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hRWc : Rf t₁ ∪ W ⊆ c.source) {z : M₂} (hzD : z ∈ tgtD s)
    (hzV : ∀ w, z ∈ section34VertexBallImage src f₁ w →
      section34VertexBallImage src f₁ w ⊆ W) :
    ∃ U ∈ 𝓝 z, U ∩ frontier W ⊆ Rf t₁ ∪ Rf t₂ := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨hD1, -, -, -, hD5, -⟩ := id hdisk
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hR₁c : IsClosed (Rf t₁) := (hR t₁).isCompact.isClosed
  have hR₂c : IsClosed (Rf t₂) := (hR t₂).isCompact.isClosed
  have hb := hdisk.interior_residual_inter_residual_eq_empty hR hDR hfr hint h7 h9 ht
  let V := {u : Section34VertexIndex 𝒦 𝒦' |
    Section34Incident u.1 t₂.1 ∧ z ∉ section34VertexBallImage src f₁ u}
  let D := {s' : Section34SimplexIndex 𝒦 3 |
    Section34Incident s'.1 t₂.1 ∧ z ∉ tgtD s'}
  let F := (⋃ u ∈ V, section34VertexBallImage src f₁ u) ∪ ⋃ s' ∈ D, tgtD s'
  have hVfin : V.Finite := (finite_setOf_section34Incident_graphIndex
    hcut.2.1 (graphSkeletonSpace 𝒦) 1 t₂.2.1).subset fun u hu => hu.1
  have hDfin : D.Finite := (finite_setOf_section34Incident t₂).subset fun s' hs' => hs'.1
  have hFc : IsClosed F := (hVfin.isClosed_biUnion fun u _ => hVc u).union
    (hDfin.isClosed_biUnion fun s' _ => hDc s')
  have hzF : z ∉ F := by
    rintro (hz | hz)
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      exact hu.2 hzu
    · obtain ⟨s', hs', hzs'⟩ := mem_iUnion₂.mp hz
      exact hs'.2 hzs'
  have hDsub : tgtD s ⊆ Rf t₁ := fun q hq => hR₁c.frontier_subset (hDR t₁ s hs₁ hq)
  have hRO : Fᶜ ∩ frontier (Rf t₂) ⊆ Rf t₁ ∪ W := by
    rintro q ⟨hqF, hqR⟩
    rcases hfr t₂ hqR with hq | hq
    · obtain ⟨u, hut, hqu⟩ := mem_iUnion₂.mp hq
      by_cases hzu : z ∈ section34VertexBallImage src f₁ u
      · exact Or.inr (hzV u hzu hqu)
      · exact (hqF (Or.inl (mem_iUnion₂.mpr ⟨u, ⟨hut, hzu⟩, hqu⟩))).elim
    · obtain ⟨s', hst, hqs'⟩ := mem_iUnion₂.mp hq
      by_cases hzs' : z ∈ tgtD s'
      · have hss : s' = s := by
          by_contra hne
          exact Set.disjoint_left.mp (hD5 s' s hne) hzs' hzD
        rw [hss] at hqs'
        exact Or.inl (hDsub hqs')
      · exact (hqF (Or.inr (mem_iUnion₂.mpr ⟨s', ⟨hst, hzs'⟩, hqs'⟩))).elim
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
    have hzc := (hR t₂).subset_closure_interior hz₂
    obtain ⟨q, hq, hq'⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
    exact Set.disjoint_left.mp hintd hq' hq
  obtain ⟨U, hU, -, hUR⟩ := hRW.exists_mem_nhds_of_inter_frontier_subset_in_chart (hR t₂) hc hRWc
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
