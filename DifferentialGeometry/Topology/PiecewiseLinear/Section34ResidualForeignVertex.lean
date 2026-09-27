/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExteriorComponent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualLocalSide

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
theorem Section34NormalPlus.residual_inter_vertexBallImage_eq_empty
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
    (hRH : R ⊆ H t.1) {w' : Section34VertexIndex 𝒦 𝒦'}
    (hw' : ¬ Section34Incident w'.1 t.1) :
    R ∩ section34VertexBallImage src f₁ w' = ∅ := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨-, -, -, hext, -, -, -, -, -, -, -, -, hfbl, -⟩ := id hdata
  have hDfbl : ∀ s, tgtD s ⊆ fbl s := fun s =>
    (hdisk.2.1 s).trans (hfbl s).boundary_subset
  have hRc : IsClosed R := hR.isCompact.isClosed
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hVconn : ∀ u, IsConnected (interior (section34VertexBallImage src f₁ u)) := by
    intro u
    exact (hVball u).isConnected_of_sdiff_subset
      (by rw [(hVball u).sdiff_boundary_eq_interior]) interior_subset
  obtain ⟨hD1, -, -, -, -, -, -, hD8, -⟩ := hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hnot : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      ¬ Section34Incident w'.1 s.1 := fun s hs hws =>
    hw' fun z hz => convexHull_min hs (convex_convexHull ℝ _) (hws hz)
  have hDV : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      ∀ z ∈ section34VertexBallImage src f₁ w', z ∉ tgtD s := by
    intro s hs z hzV hzD
    have h0 : z ∈ tgtD s ∩ section34VertexBallImage src f₁ w' := ⟨hzD, hzV⟩
    rw [hD8 s w' (hnot s hs)] at h0
    exact h0
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w'.2.2.1
  have hpw : p ∈ (w'.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  let y := h (𝒦'.map p)
  have hycore : y ∈ h '' simplexBody 𝒦' w'.1 :=
    ⟨𝒦'.map p, ⟨p, subset_convexHull ℝ _ hpw, rfl⟩, rfl⟩
  have hyint : y ∈ interior (section34VertexBallImage src f₁ w') := hext.2.1 w' hycore
  obtain ⟨O, hO⟩ : ∃ O : Set M₂,
      O = section34TetraObstacle (section34VertexBallImage src f₁) fbl t :=
    ⟨_, rfl⟩
  have hfrO : frontier R ⊆ O := by
    rw [hO]
    intro z hz
    rcases hfr hz with hz | hz
    · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz
      exact Or.inl (mem_iUnion₂.mpr ⟨⟨(t, u), hu⟩, rfl, hzu⟩)
    · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz
      exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hDfbl s hzs⟩)
  have hfrHi : frontier R ⊆ interior (H t.1) := by
    rw [hO] at hfrO
    exact hfrO.trans (hext.1 t)
  have hboundary : Disjoint (frontier (H t.1)) R := by
    refine Set.disjoint_left.mpr fun z hzH hzR => ?_
    have hzfr : z ∈ frontier R :=
      ⟨subset_closure hzR, fun hzi => hzH.2 (interior_mono hRH hzi)⟩
    exact hzH.2 (hfrHi hzfr)
  have hyR : y ∉ R := by
    by_cases hyH : y ∈ H t.1
    · obtain ⟨hyO, q, hqC, hqH⟩ := hext.2.2 t w' hw' y hycore hyH
      rw [← hO] at hyO hqC
      have havoid : Disjoint (connectedComponentIn (H t.1 \ O) y) (frontier R) := by
        refine Set.disjoint_left.mpr fun z hz hzR => ?_
        exact (connectedComponentIn_subset (H t.1 \ O) y hz).2 (hfrO hzR)
      rcases DifferentialGeometry.Topology.subset_interior_or_subset_compl_of_disjoint_frontier
        hRc (isPreconnected_connectedComponentIn (F := H t.1 \ O) (x := y)) havoid
        with hsub | hsub
      · exact (Set.disjoint_left.mp hboundary hqH (interior_subset (hsub hqC))).elim
      · exact hsub (mem_connectedComponentIn ⟨hyH, hyO⟩)
    · exact fun hyr => hyH (hRH hyr)
  have hintV : interior (section34VertexBallImage src f₁ w') ⊆ Rᶜ := by
    have hdisj : Disjoint (interior (section34VertexBallImage src f₁ w'))
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
    rcases DifferentialGeometry.Topology.subset_interior_or_subset_compl_of_disjoint_frontier
      hRc
      (hVconn w').isPreconnected hdisj with hsub | hsub
    · exact absurd (interior_subset (hsub hyint)) hyR
    · exact hsub
  have hRVfr : ∀ z ∈ R, z ∈ section34VertexBallImage src f₁ w' → z ∈ frontier R := by
    intro z hzR hzV
    refine ⟨subset_closure hzR, fun hzi => ?_⟩
    have hzc : z ∈ closure (interior (section34VertexBallImage src f₁ w')) :=
      (hVball w').subset_closure_interior hzV
    obtain ⟨q, hqR, hqV⟩ := mem_closure_iff.mp hzc (interior R) isOpen_interior hzi
    exact hintV hqV (interior_subset hqR)
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨hzR, hzV⟩ := hz
  rcases hfr (hRVfr z hzR hzV) with hz' | hz'
  · obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hz'
    have hne : u ≠ w' := by
      rintro rfl
      exact hw' hu
    have hzfr : z ∈ frontier (section34VertexBallImage src f₁ u) :=
      ⟨subset_closure hzu, fun hzi =>
        Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hne) hzi hzV⟩
    obtain ⟨U, hU, -, hUR⟩ := hdata.exists_mem_nhds_frontier_subset_residual hR hfr hint hDc
      (hVball u) (subset_iUnion₂_of_subset u hu subset_rfl) hzR hzfr
      (fun v hv hzv => by
        by_cases hvu : v = u
        · subst hvu
          exact subset_rfl
        · have hvw : v ≠ w' := by
            rintro rfl
            exact hw' hv
          have h0 : z ∈ section34VertexBallImage src f₁ v ∩
              section34VertexBallImage src f₁ u ∩
              section34VertexBallImage src f₁ w' := ⟨⟨hzv, hzu⟩, hzV⟩
          rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁.injOn hvu hvw hne] at h0
          exact h0.elim)
      (fun s hs => hDV s hs z hzV)
    have hzc : z ∈ closure (interior (section34VertexBallImage src f₁ w')) :=
      (hVball w').subset_closure_interior hzV
    obtain ⟨q, hqU, hqV⟩ := mem_closure_iff_nhds.mp hzc U hU
    have hqu : q ∉ section34VertexBallImage src f₁ u := fun hqu =>
      Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hne.symm) hqV hqu
    exact hintV hqV (interior_subset (hUR ⟨hqU, hqu⟩))
  · obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz'
    exact hDV s hs z hzV hzs

omit [FiniteDimensional ℝ Ea] [MetricSpace M₂] [ChartedSpace E3 M₂] in
theorem Section34CutFrame.residual_inter_splitDiskImage_eq_empty
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : InjOn f₁ (section34CutNeighborhood src))
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂}
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {e : Section34EdgeIndex 𝒦 𝒦'} (he : ¬ Section34Incident e.1 t.1) :
    R ∩ section34SplitDiskImage src f₁ e = ∅ := by
  obtain ⟨a, b, -, habe, hE⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  rw [hE]
  by_cases ha : Section34Incident a.1 t.1
  · by_cases hb : Section34Incident b.1 t.1
    · refine absurd ?_ he
      change (e.1 : Set Ea) ⊆ _
      rw [habe]
      exact union_subset ha hb
    · exact subset_eq_empty (inter_subset_inter_right _ inter_subset_right) (h7 b hb)
  · exact subset_eq_empty (inter_subset_inter_right _ inter_subset_left) (h7 a ha)

end DifferentialGeometry.Topology.PiecewiseLinear
