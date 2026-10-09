/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPairs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBoundaryIncidence

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactCutFrame.exists_simplexIndex_four_of_edge
    (hcut : Section34CompactCutFrame C K K' src srcBd) (e : Section34CompactEdgeIndex K K') :
    ∃ t : Section34CompactSimplexIndex K 4, Section34Incident e.1 t.1 := by
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨-, hK, -, hman, hsub, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hex⟩ := id hcut
  let _ : Finite K.faces := hK.to_subtype
  have hne : e.1.Nonempty := Finset.card_pos.mp (by rw [e.2.2.1]; norm_num)
  have hm := centroid_mem_openSimplex hne
  have hmconv : e.1.centroid ℝ id ∈ convexHull ℝ (e.1 : Set E3) :=
    openSimplex_subset_convexHull e.1 hm
  obtain ⟨σ, ⟨hσ, hσcard⟩, hmσ⟩ := mem_iUnion₂.mp (e.2.2.2 hmconv)
  have heσ : convexHull ℝ (e.1 : Set E3) ⊆ convexHull ℝ (σ : Set E3) :=
    hsub.convexHull_subset_of_mem_openSimplex hσ e.2.1 hm hmσ
  have hσ2 : σ.card = 1 + 1 := by
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hσ)
    by_contra hne2
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (by omega : σ.card = 1)
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp e.2.2.1
    have ha : a ∈ convexHull ℝ (({u} : Finset E3) : Set E3) :=
      heσ (subset_convexHull ℝ _ (by rw [heab]; simp))
    have hb : b ∈ convexHull ℝ (({u} : Finset E3) : Set E3) :=
      heσ (subset_convexHull ℝ _ (by rw [heab]; simp))
    rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at ha hb
    exact hab (ha.trans hb.symm)
  rcases hman.isPLSphere_or_isPLBall_geometricLink (n := 2) K hσ hσ2
    (by norm_num) with hL | hL
  all_goals
    obtain ⟨x, hx⟩ := hL.nonempty
    obtain ⟨ρ, hρ, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := hρ.1
    have hvσ : v ∉ σ := Finset.disjoint_right.mp hρ.2.1 hv
    have hτ : insert v σ ∈ K.faces := K.down_closed hρ.2.2
      (fun z hz => (Finset.mem_insert.mp hz).elim (fun h => by
        rw [h]
        exact Finset.mem_union_right _ hv) fun h => Finset.mem_union_left _ h)
      (Finset.insert_nonempty _ _)
    obtain ⟨t, ht⟩ := hex ⟨insert v σ, hτ, by rw [Finset.card_insert_of_notMem hvσ, hσ2]⟩
    refine ⟨t, fun z hz => ?_⟩
    have hz := heσ (subset_convexHull ℝ _ hz)
    exact convexHull_min ht (convex_convexHull ℝ _)
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert v σ)) hz)

theorem Section34CompactCutFrame.exists_edgeIndex_of_vertex
    (hcut : Section34CompactCutFrame C K K' src srcBd) (w : Section34CompactVertexIndex K K') :
    ∃ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 := by
  obtain ⟨-, hK, -, hman, -⟩ := id hcut
  let _ : Finite K.faces := hK.to_subtype
  obtain ⟨p, hwp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ convexHull ℝ (w.1 : Set E3) := by
    rw [hwp, Finset.coe_singleton, convexHull_singleton]
    exact mem_singleton p
  obtain ⟨σ, ⟨hσ, hσcard⟩, hpσ⟩ := mem_iUnion₂.mp (w.2.2.2 hpw)
  obtain ⟨u, v, huv, huvK, hp⟩ : ∃ u v : E3, u ≠ v ∧ ({u, v} : Finset E3) ∈ K.faces ∧
      p ∈ segment ℝ u v := by
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hσ)
    by_cases h2 : σ.card = 2
    · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h2
      refine ⟨u, v, huv, hσ, ?_⟩
      rw [← convexHull_pair, ← Finset.coe_pair]
      exact hpσ
    · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (by omega : σ.card = 1)
      rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hpσ
      rcases hman.isPLSphere_or_isPLBall_geometricLink (n := 2) K hσ (k := 0)
        (by rw [Finset.card_singleton]) (by norm_num)
        with hL | hL
      all_goals
        obtain ⟨v, τ, hvu, hτ, huτ, hvτ⟩ : ∃ (v : E3) (τ : Finset E3), v ≠ u ∧ τ ∈ K.faces ∧
            u ∈ τ ∧ v ∈ τ := by
          let _ : DecidableEq E3 := Classical.decEq E3
          obtain ⟨x, hx⟩ := hL.nonempty
          obtain ⟨ρ, hρ, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
          obtain ⟨v, hv⟩ := hρ.1
          exact ⟨v, _, fun h => Finset.disjoint_right.mp hρ.2.1 hv (by rw [h]; simp), hρ.2.2,
            Finset.mem_union_left _ (Finset.mem_singleton_self u), Finset.mem_union_right _ hv⟩
        exact ⟨u, v, hvu.symm, K.down_closed hτ
          (Finset.insert_subset huτ (Finset.singleton_subset_iff.mpr hvτ))
          (Finset.insert_nonempty _ _), by rw [hpσ]; exact left_mem_segment ℝ u v⟩
  obtain ⟨n, wv, ev, hn, -, -, -, hev, -, hsurj, -⟩ := hcut.exists_vertexIndex_path huv huvK
  obtain ⟨i, hi, rfl⟩ := hsurj w ⟨p, hp, hwp⟩
  rcases Nat.lt_or_ge i n with h | h
  · refine ⟨ev i, ?_⟩
    rw [hev i h]
    exact Finset.subset_union_left
  · refine ⟨ev (i - 1), ?_⟩
    rw [hev (i - 1) (by omega), show i - 1 + 1 = i by omega]
    exact Finset.subset_union_right

theorem Section34CompactCutFrame.isPLBall_residual_union_vertexBallImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t.1) :
    IsPLBall 3 (R ∪ section34CompactVertexBallImage src f₁ w) := by
  obtain ⟨q, hq, -⟩ := hcut.exists_residualPatch_boundary hf₁ hdisk hR hDR hfr hint hio h7 hw
  exact isPLBall_union_of_inter_eq_of_subset_frontier hR
    (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three ⟨q, hq⟩ rfl
    (residual_inter_vertexBallImage_subset_frontier hR hint hw)

theorem Section34CompactCutFrame.isPLBall_residual_union_vertexBallImage_pair
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {e : Section34CompactEdgeIndex K K'} (he : Section34Incident e.1 t.1)
    {w w' : Section34CompactVertexIndex K K'} (hww' : w ≠ w') (hwe : w.1 ⊆ e.1)
    (hw'e : w'.1 ⊆ e.1) :
    IsPLBall 3 (R ∪ (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ w')) := by
  have hw : Section34Incident w.1 t.1 := fun z hz => he (hwe hz)
  have hw' : Section34Incident w'.1 t.1 := fun z hz => he (hw'e hz)
  have hB1 := hcut.isPLBall_residual_union_vertexBallImage hf₁ hdisk hR hDR hfr hint hio h7 hw
  obtain ⟨q', hq', hq'b⟩ :=
    hcut.exists_residualPatch_boundary hf₁ hdisk hR hDR hfr hint hio h7 hw'
  obtain ⟨γ, hγ, -⟩ := hcut.exists_residualEdgeArc hf₁ hdisk hR hDR hfr hint hio h7 he
  obtain ⟨rE, hrE, hrEb⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  have hEw' : section34CompactSplitDiskImage src f₁ e ⊆
      section34CompactVertexBallImage src f₁ w' := by
    rw [← hinter]
    exact inter_subset_right
  have hPE : R ∩ section34CompactVertexBallImage src f₁ w' ∩
      section34CompactSplitDiskImage src f₁ e = R ∩ section34CompactSplitDiskImage src f₁ e := by
    rw [inter_assoc, inter_eq_right.mpr hEw']
  have hIq' : R ∩ section34CompactSplitDiskImage src f₁ e ⊆ q' '' stdSimplexBoundary 2 := by
    rw [hq'b]
    intro z hz
    exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, e), he⟩, ⟨rfl, hw'e⟩, hz⟩)
  have hIE : R ∩ section34CompactSplitDiskImage src f₁ e ⊆ rE '' stdSimplexBoundary 2 := by
    rw [← hrEb]
    exact hcut.residual_inter_splitDiskImage_subset hf₁ hR hint h7 e
  obtain ⟨qd, hqd, -⟩ := exists_isPLHomeomorphOn_union_of_inter_eq_arc hq' hrE hγ hPE hIq' hIE
  have hmeet : (R ∪ section34CompactVertexBallImage src f₁ w) ∩
      section34CompactVertexBallImage src f₁ w' =
      R ∩ section34CompactVertexBallImage src f₁ w' ∪ section34CompactSplitDiskImage src f₁ e := by
    rw [union_inter_distrib_right, hinter]
  have hsubfr : R ∩ section34CompactVertexBallImage src f₁ w' ∪
      section34CompactSplitDiskImage src f₁ e ⊆
        frontier (section34CompactVertexBallImage src f₁ w') :=
    union_subset (residual_inter_vertexBallImage_subset_frontier hR hint hw')
      (hcut.splitDiskImage_subset_frontier hf₁ hw'e)
  have h := isPLBall_union_of_inter_eq_of_subset_frontier hB1
    (hcut.isPLCellOn_vertexBallImage hf₁ w').isPLBall_three ⟨qd, hqd⟩ hmeet hsubfr
  rwa [union_assoc] at h

theorem Section34CompactCutFrame.exists_mem_nhds_frontier_pair_subset_iUnion_residual
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
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {e : Section34CompactEdgeIndex K K'}
    {w w' : Section34CompactVertexIndex K K'} (hww' : w ≠ w') (hwe : w.1 ⊆ e.1)
    (hw'e : w'.1 ⊆ e.1) {z : E3} (hzb : z ∈ section34CompactSplitDiskImage srcBd f₁ e)
    (hzs : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident e.1 s.1 → z ∈ tgtD s →
      ¬ convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space)
    {t : Section34CompactSimplexIndex K 4} (het : Section34Incident e.1 t.1) (hzR : z ∈ Rf t) :
    ∃ U ∈ 𝓝 z, U ∩ frontier (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ w') ⊆
        ⋃ (t' : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t'.1), Rf t' := by
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  obtain ⟨qE, hqE, -⟩ := hEcell.exists_isPLHomeomorphOn_stdSimplex
  have hW := isPLBall_union_of_inter_eq_of_subset_frontier (hVball w) (hVball w') ⟨qE, hqE⟩
    hinter (hcut.splitDiskImage_subset_frontier hf₁ hw'e)
  have hzW : z ∈ frontier (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ w') :=
    boundary_subset_frontier_union_of_inter_eq (hVball w) (hVball w') hEcell hinter
      (hcut.splitDiskImage_subset_frontier hf₁ hwe) hzb
  have hzE : z ∈ section34CompactSplitDiskImage src f₁ e := hEcell.boundary_subset hzb
  have hzww : z ∈ section34CompactVertexBallImage src f₁ w ∩
      section34CompactVertexBallImage src f₁ w' := by
    rw [hinter]
    exact hzE
  have hzV : ∀ u, z ∈ section34CompactVertexBallImage src f₁ u →
      section34CompactVertexBallImage src f₁ u ⊆
        section34CompactVertexBallImage src f₁ w ∪ section34CompactVertexBallImage src f₁ w' := by
    intro u hzu
    by_cases huw : u = w
    · rw [huw]
      exact subset_union_left
    · by_cases huw' : u = w'
      · rw [huw']
        exact subset_union_right
      · have h0 : z ∈ section34CompactVertexBallImage src f₁ u ∩
            section34CompactVertexBallImage src f₁ w ∩
            section34CompactVertexBallImage src f₁ w' := ⟨⟨hzu, hzww.1⟩, hzww.2⟩
        rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ huw huw' hww'] at h0
        exact h0.elim
  have hWt : ∀ t' : Section34CompactSimplexIndex K 4, Section34Incident e.1 t'.1 →
      section34CompactVertexBallImage src f₁ w ∪ section34CompactVertexBallImage src f₁ w' ⊆
        ⋃ (u : Section34CompactVertexIndex K K') (_ : Section34Incident u.1 t'.1),
          section34CompactVertexBallImage src f₁ u := fun t' het' =>
    union_subset (subset_iUnion₂_of_subset w (fun x hx => het' (hwe hx)) subset_rfl)
      (subset_iUnion₂_of_subset w' (fun x hx => het' (hw'e hx)) subset_rfl)
  by_cases hzD : ∃ s, z ∈ tgtD s
  · obtain ⟨s, hzs'⟩ := hzD
    have hes : Section34Incident e.1 s.1 := by
      by_contra hes
      have h0 : z ∈ tgtD s ∩ section34CompactSplitDiskImage src f₁ e := ⟨hzs', hzE⟩
      rw [hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁ hes] at h0
      exact h0
    obtain ⟨t₁, t₂, ht12, hs1, hs2⟩ :=
      hcut.exists_tetra_pair_of_not_boundary_triangle s (hzs s hes hzs')
    have he1 : Section34Incident e.1 t₁.1 := fun x hx =>
      convexHull_min hs1 (convex_convexHull ℝ _) (hes hx)
    have he2 : Section34Incident e.1 t₂.1 := fun x hx =>
      convexHull_min hs2 (convex_convexHull ℝ _) (hes hx)
    have hRW := hcut.isPLBall_residual_union_vertexBallImage_pair hf₁ hdisk (hR t₁) (hDR t₁)
      (hfr t₁) (hint t₁) (hio t₁) (h7 t₁) he1 hww' hwe hw'e
    obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_union hf₁ hdisk hR hDR hfr hint
      h7 h9 ht12 hs1 hs2 (hWt t₂ he2) hRW hzs' hzV
    refine ⟨U, hU, fun q hq => ?_⟩
    rcases hUR hq with h | h
    · exact mem_iUnion₂.mpr ⟨t₁, he1, h⟩
    · exact mem_iUnion₂.mpr ⟨t₂, he2, h⟩
  · obtain ⟨U, hU, hUR, -⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ (hR t) (hfr t)
      (hint t) hDc hW (hWt t het) hzR hzW (fun u _ hzu => hzV u hzu)
      (fun s _ hzs => hzD ⟨s, hzs⟩)
    exact ⟨U, hU, fun q hq => mem_iUnion₂.mpr ⟨t, het, hUR hq⟩⟩

theorem Section34CompactCutFrame.splitDiskImage_boundary_subset_iUnion_residual
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
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    (e : Section34CompactEdgeIndex K K')
    (he : ¬ convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space) :
    section34CompactSplitDiskImage srcBd f₁ e ⊆
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
  obtain ⟨-, hKfin, -⟩ := id hcut
  have _ := finite_section34CompactSimplexIndex hKfin 4
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hEc : IsClosed (section34CompactSplitDiskImage src f₁ e) := hEcell.isCompact.isClosed
  obtain ⟨w, w', hww', hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hwe : w.1 ⊆ e.1 := by
    have h : (w.1 : Set E3) ⊆ e.1 := by
      rw [hew]
      exact subset_union_left
    exact Finset.coe_subset.mp h
  have hw'e : w'.1 ⊆ e.1 := by
    have h : (w'.1 : Set E3) ⊆ e.1 := by
      rw [hew]
      exact subset_union_right
    exact Finset.coe_subset.mp h
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  have hEbW : section34CompactSplitDiskImage srcBd f₁ e ⊆
      frontier (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ w') :=
    boundary_subset_frontier_union_of_inter_eq (hVball w) (hVball w') hEcell hinter
      (hcut.splitDiskImage_subset_frontier hf₁ hwe)
  have hCovc : IsClosed (⋃ (t : Section34CompactSimplexIndex K 4)
      (_ : Section34Incident e.1 t.1), Rf t ∩ section34CompactSplitDiskImage src f₁ e) :=
    isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
      (hR t).isPolyhedron.isClosed.inter hEc
  have hloc : ∀ z ∈ section34CompactSplitDiskImage srcBd f₁ e,
      z ∈ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34CompactSplitDiskImage src f₁ e →
      ∃ U ∈ 𝓝 z, U ∩ section34CompactSplitDiskImage srcBd f₁ e ⊆
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
    intro z hzb hz
    obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp hz
    obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_pair_subset_iUnion_residual hf₁ hdisk
      hR hDR hfr hint hio h7 h9 hww' hwe hw'e hzb
      (fun s hes _ h => he ((convexHull_min hes (convex_convexHull ℝ _)).trans h)) het hzR
    refine ⟨U, hU, fun q hq => ?_⟩
    obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp (hUR ⟨hq.1, hEbW hq.2⟩)
    exact mem_iUnion₂.mpr ⟨t', het', hqR, hEcell.boundary_subset hq.2⟩
  rcases subset_or_disjoint_of_isPreconnected_of_locally_subset
    hEcell.isPLSphere_one_of_two.isConnected.isPreconnected hCovc hloc with h | h
  · exact h
  · exfalso
    obtain ⟨t, het⟩ := hcut.exists_simplexIndex_four_of_edge e
    obtain ⟨γ, hγ, -⟩ := hcut.exists_residualEdgeArc hf₁ hdisk (hR t) (hDR t) (hfr t) (hint t)
      (hio t) (h7 t) het
    have hq : γ 0 ∈ Rf t ∩ section34CompactSplitDiskImage src f₁ e :=
      hγ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    exact Set.disjoint_left.mp h
      (hcut.residual_inter_splitDiskImage_subset hf₁ (hR t) (hint t) (h7 t) e hq)
      (mem_iUnion₂.mpr ⟨t, het, hq⟩)

theorem Section34CompactCutFrame.vertexBallImage_frontier_subset_iUnion_residual
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
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    (w : Section34CompactVertexIndex K K') (hw : ¬ (w.1 : Set E3) ⊆ frontier K.space) :
    frontier (section34CompactVertexBallImage src f₁ w) ⊆
      (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w := by
  obtain ⟨-, hKfin, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactSimplexIndex hKfin 4
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 2
  obtain ⟨hD1, -, -, -, -, -, -, hD8, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hVball u).isPolyhedron.isClosed
  have hEc : ∀ e, IsClosed (section34CompactSplitDiskImage src f₁ e) := fun e =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).isCompact.isClosed
  have hCovc : IsClosed ((⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w) :=
    (isClosed_iUnion_of_finite fun e => isClosed_iUnion_of_finite fun _ => hEc e).union
      (isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
        (hR t).isPolyhedron.isClosed.inter (hVc w))
  have hcapCov : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      ∀ q ∈ section34CompactSplitDiskImage src f₁ e,
      q ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w := fun e he q hq =>
    Or.inl (mem_iUnion₂.mpr ⟨e, he, hq⟩)
  have hpatchCov : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident w.1 t.1 →
      ∀ q ∈ Rf t, q ∈ section34CompactVertexBallImage src f₁ w →
      q ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w := fun t ht q hq hqV =>
    Or.inr (mem_iUnion₂.mpr ⟨t, ht, hq, hqV⟩)
  have hloc : ∀ z ∈ frontier (section34CompactVertexBallImage src f₁ w),
      z ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w →
      ∃ U ∈ 𝓝 z, U ∩ frontier (section34CompactVertexBallImage src f₁ w) ⊆
        (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
          section34CompactSplitDiskImage src f₁ e) ∪
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
          Rf t ∩ section34CompactVertexBallImage src f₁ w := by
    intro z hzS hz
    by_cases hzcap : ∃ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 ∧
        z ∈ section34CompactSplitDiskImage src f₁ e
    · obtain ⟨e, hwe, hzE⟩ := hzcap
      obtain ⟨w', hww', hw'e⟩ : ∃ w' : Section34CompactVertexIndex K K', w ≠ w' ∧
          w'.1 ⊆ e.1 := by
        obtain ⟨a, b, hab, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
        have hae : a.1 ⊆ e.1 := by
          have h : (a.1 : Set E3) ⊆ e.1 := by
            rw [habe]
            exact subset_union_left
          exact Finset.coe_subset.mp h
        have hbe : b.1 ⊆ e.1 := by
          have h : (b.1 : Set E3) ⊆ e.1 := by
            rw [habe]
            exact subset_union_right
          exact Finset.coe_subset.mp h
        rcases eq_or_eq_of_section34CompactVertexIndex_subset e habe hwe with h | h
        · exact ⟨b, by rw [h]; exact hab, hbe⟩
        · exact ⟨a, by rw [h]; exact hab.symm, hae⟩
      have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
      have hEcap : ∀ q ∈ frontier (section34CompactVertexBallImage src f₁ w),
          q ∈ section34CompactVertexBallImage src f₁ w' →
          q ∈ (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
            section34CompactSplitDiskImage src f₁ e) ∪
          ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
            Rf t ∩ section34CompactVertexBallImage src f₁ w := fun q hq hqw' =>
        hcapCov e hwe q (by rw [← hinter]; exact ⟨(hVc w).frontier_subset hq, hqw'⟩)
      have hei : ¬ convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space := fun h =>
        hw fun x hx => h (subset_convexHull ℝ _ (hwe hx))
      by_cases hzb : z ∈ section34CompactSplitDiskImage srcBd f₁ e
      · obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp
          (hcut.splitDiskImage_boundary_subset_iUnion_residual hf₁ hdisk hR hDR hfr hint hio h7
            h9 e hei hzb)
        obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_pair_subset_iUnion_residual hf₁
          hdisk hR hDR hfr hint hio h7 h9 hww' hwe hw'e hzb
          (fun s hes _ h => hei ((convexHull_min hes (convex_convexHull ℝ _)).trans h)) het hzR
        refine ⟨U, hU, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34CompactVertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp
            (hUR ⟨hq.1, mem_frontier_union_of_notMem (hVc w') hq.2 hqw'⟩)
          exact hpatchCov t' (fun x hx => het' (hwe hx)) q hqR ((hVc w).frontier_subset hq.2)
      · have hzi : z ∈ interior (⋃ u, section34CompactVertexBallImage src f₁ u) :=
          hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hzE, hzb⟩
        have hFc : IsClosed (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u) :=
          isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ => hVc u
        have hzww : z ∈ section34CompactVertexBallImage src f₁ w ∩
            section34CompactVertexBallImage src f₁ w' := by
          rw [hinter]
          exact hzE
        have hzF : z ∉ ⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u := by
          intro h
          obtain ⟨u, ⟨huw, huw'⟩, hzu⟩ := mem_iUnion₂.mp h
          have h0 : z ∈ section34CompactVertexBallImage src f₁ u ∩
              section34CompactVertexBallImage src f₁ w ∩
              section34CompactVertexBallImage src f₁ w' := ⟨⟨hzu, hzww.1⟩, hzww.2⟩
          rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ huw huw' hww'] at h0
          exact h0
        refine ⟨interior (⋃ u, section34CompactVertexBallImage src f₁ u) ∩
          (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u)ᶜ,
          (isOpen_interior.inter hFc.isOpen_compl).mem_nhds ⟨hzi, hzF⟩, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34CompactVertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · exfalso
          refine hq.2.2 (mem_interior.mpr
            ⟨interior (⋃ u, section34CompactVertexBallImage src f₁ u) ∩
            (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
              section34CompactVertexBallImage src f₁ u)ᶜ ∩
            (section34CompactVertexBallImage src f₁ w')ᶜ, fun y hy => ?_,
            (isOpen_interior.inter hFc.isOpen_compl).inter (hVc w').isOpen_compl,
            ⟨hq.1, hqw'⟩⟩)
          obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
          obtain ⟨u, hyu⟩ := mem_iUnion.mp (interior_subset hy1)
          by_cases huw : u = w
          · rw [← huw]
            exact hyu
          · by_cases huw' : u = w'
            · rw [huw'] at hyu
              exact absurd hyu hy3
            · exact absurd (mem_iUnion₂.mpr ⟨u, ⟨huw, huw'⟩, hyu⟩) hy2
    · rcases hz with hz | hz
      · obtain ⟨e, he, hzE⟩ := mem_iUnion₂.mp hz
        exact absurd ⟨e, he, hzE⟩ hzcap
      · obtain ⟨t, htw, hzR, hzV⟩ := mem_iUnion₂.mp hz
        have hzV' : ∀ u, z ∈ section34CompactVertexBallImage src f₁ u →
            section34CompactVertexBallImage src f₁ u ⊆
              section34CompactVertexBallImage src f₁ w := by
          intro u hzu
          by_cases huw : u = w
          · exact (congrArg (section34CompactVertexBallImage src f₁) huw).subset
          · exfalso
            obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ huw hzu hzV
            exact hzcap ⟨e, hcut.subset_of_mem_splitDiskImage hf₁ hze hzV, hze⟩
        by_cases hzD : ∃ s, z ∈ tgtD s
        · obtain ⟨s, hzs⟩ := hzD
          have hws : Section34Incident w.1 s.1 := by
            by_contra hws
            have h0 : z ∈ tgtD s ∩ section34CompactVertexBallImage src f₁ w := ⟨hzs, hzV⟩
            rw [hD8 s w hws] at h0
            exact h0
          have hsi : ¬ convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space := fun h =>
            hw (Set.Subset.trans hws h)
          obtain ⟨t₁, t₂, ht12, hs1, hs2⟩ := hcut.exists_tetra_pair_of_not_boundary_triangle s hsi
          have hw1 : Section34Incident w.1 t₁.1 := fun x hx =>
            convexHull_min hs1 (convex_convexHull ℝ _) (hws hx)
          have hw2 : Section34Incident w.1 t₂.1 := fun x hx =>
            convexHull_min hs2 (convex_convexHull ℝ _) (hws hx)
          have hRW := hcut.isPLBall_residual_union_vertexBallImage hf₁ hdisk (hR t₁) (hDR t₁)
            (hfr t₁) (hint t₁) (hio t₁) (h7 t₁) hw1
          obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_union hf₁ hdisk hR hDR hfr
            hint h7 h9 ht12 hs1 hs2 (subset_iUnion₂_of_subset w hw2 subset_rfl) hRW hzs hzV'
          refine ⟨U, hU, fun q hq => ?_⟩
          rcases hUR hq with h | h
          · exact hpatchCov t₁ hw1 q h ((hVc w).frontier_subset hq.2)
          · exact hpatchCov t₂ hw2 q h ((hVc w).frontier_subset hq.2)
        · obtain ⟨U, hU, hUR, -⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ (hR t)
            (hfr t) (hint t) hDc (hVball w) (subset_iUnion₂_of_subset w htw subset_rfl) hzR hzS
            (fun u _ hzu => hzV' u hzu) (fun s _ hzs => hzD ⟨s, hzs⟩)
          exact ⟨U, hU, fun q hq =>
            hpatchCov t htw q (hUR hq) ((hVc w).frontier_subset hq.2)⟩
  rcases subset_or_disjoint_of_isPreconnected_of_locally_subset
    (hVball w).isPLSphere_frontier.isConnected.isPreconnected hCovc hloc with h | h
  · exact h
  · exfalso
    obtain ⟨e, he⟩ := hcut.exists_edgeIndex_of_vertex w
    obtain ⟨q, hq⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
    exact Set.disjoint_left.mp h (hcut.splitDiskImage_subset_frontier hf₁ he hq)
      (hcapCov e he q hq)

end DifferentialGeometry.Topology.PiecewiseLinear
