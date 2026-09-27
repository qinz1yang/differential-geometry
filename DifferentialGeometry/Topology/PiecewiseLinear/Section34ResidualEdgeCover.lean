/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualCoverLocal
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraCofaces
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryConnected

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

theorem Section34NormalPlus.exists_mem_nhds_frontier_pair_subset_iUnion_residual
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34SimplexIndex 𝒦 4 → Set M₂} (hR : ∀ t, IsPLCellOn 3 (Rf t) (frontier (Rf t)))
    (hRH : ∀ t, Rf t ⊆ H t.1)
    (hDR : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34SimplexIndex 𝒦 4, frontier (Rf t) ⊆
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34SimplexIndex 𝒦 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w))
    (hio : ∀ (t : Section34SimplexIndex 𝒦 4) (a : Section34ArcIndex 𝒦 𝒦'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34VertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {e : Section34EdgeIndex 𝒦 𝒦'}
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww' : w ≠ w') (hwe : w.1 ⊆ e.1)
    (hw'e : w'.1 ⊆ e.1) {z : M₂} (hzb : z ∈ section34SplitDiskImage srcBd f₁ e)
    {t : Section34SimplexIndex 𝒦 4} (het : Section34Incident e.1 t.1) (hzR : z ∈ Rf t) :
    ∃ U ∈ 𝓝 z, U ∩ frontier (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ w') ⊆
        ⋃ (t' : Section34SimplexIndex 𝒦 4) (_ : Section34Incident e.1 t'.1), Rf t' := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  obtain ⟨c, hc, -, hVc, -⟩ := hdata.exists_chart_tetrahedron t
  have hw : Section34Incident w.1 t.1 := fun x hx => het (hwe hx)
  have hw' : Section34Incident w'.1 t.1 := fun x hx => het (hw'e hx)
  have hW := (hVball w).union_of_inter_eq_of_subset_frontier_in_chart (hVball w') hEcell
    hinter (hcut.splitDiskImage_subset_frontier hf₁ hw'e) hc (hVc w hw) (hVc w' hw')
  have hzW : z ∈ frontier (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ w') :=
    hEcell.boundary_subset_frontier_union_in_chart (hVball w) (hVball w') hinter
      (hcut.splitDiskImage_subset_frontier hf₁ hwe) hc (hVc w hw) (hVc w' hw') hzb
  have hzE : z ∈ section34SplitDiskImage src f₁ e := hEcell.boundary_subset hzb
  have hzww : z ∈ section34VertexBallImage src f₁ w ∩
      section34VertexBallImage src f₁ w' := by
    rw [hinter]
    exact hzE
  have hzV : ∀ u, z ∈ section34VertexBallImage src f₁ u →
      section34VertexBallImage src f₁ u ⊆
        section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ w' := by
    intro u hzu
    by_cases huw : u = w
    · rw [huw]
      exact subset_union_left
    · by_cases huw' : u = w'
      · rw [huw']
        exact subset_union_right
      · have h0 : z ∈ section34VertexBallImage src f₁ u ∩
            section34VertexBallImage src f₁ w ∩
            section34VertexBallImage src f₁ w' := ⟨⟨hzu, hzww.1⟩, hzww.2⟩
        rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁.injOn huw huw' hww'] at h0
        exact h0.elim
  have hWt : ∀ t' : Section34SimplexIndex 𝒦 4, Section34Incident e.1 t'.1 →
      section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ w' ⊆
        ⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident u.1 t'.1),
          section34VertexBallImage src f₁ u := fun t' het' =>
    union_subset (subset_iUnion₂_of_subset w (fun x hx => het' (hwe hx)) subset_rfl)
      (subset_iUnion₂_of_subset w' (fun x hx => het' (hw'e hx)) subset_rfl)
  by_cases hzD : ∃ s, z ∈ tgtD s
  · obtain ⟨s, hzs'⟩ := hzD
    have hes : Section34Incident e.1 s.1 := by
      by_contra hes
      have h0 : z ∈ tgtD s ∩ section34SplitDiskImage src f₁ e := ⟨hzs', hzE⟩
      rw [hdisk.faceDisk_inter_splitDisk_eq_empty hdata hes] at h0
      exact h0
    obtain ⟨t₁, t₂, ht12, hs1, hs2⟩ :=
      hcut.exists_tetra_pair_of_triangle s
    have he1 : Section34Incident e.1 t₁.1 := fun x hx =>
      convexHull_min hs1 (convex_convexHull ℝ _) (hes hx)
    have he2 : Section34Incident e.1 t₂.1 := fun x hx =>
      convexHull_min hs2 (convex_convexHull ℝ _) (hes hx)
    have hRW := hdata.isPLCellOn_residual_union_vertexBallImage_pair hdisk (hR t₁) (hRH t₁) (hDR t₁)
      (hfr t₁) (hint t₁) (hio t₁) (h7 t₁) he1 hww' hwe hw'e
    obtain ⟨c₁, hc₁, hHc₁, hVc₁, -⟩ := hdata.exists_chart_tetrahedron t₁
    have hRWc : Rf t₁ ∪ (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ w') ⊆ c₁.source :=
      union_subset ((hRH t₁).trans hHc₁)
        (union_subset (hVc₁ w (fun x hx => he1 (hwe hx)))
          (hVc₁ w' (fun x hx => he1 (hw'e hx))))
    obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_frontier_subset_union hdisk hR hDR hfr hint
      h7 h9 ht12 hs1 hs2 (hWt t₂ he2) hRW hc₁ hRWc hzs' hzV
    refine ⟨U, hU, fun q hq => ?_⟩
    rcases hUR hq with h | h
    · exact mem_iUnion₂.mpr ⟨t₁, he1, h⟩
    · exact mem_iUnion₂.mpr ⟨t₂, he2, h⟩
  · obtain ⟨U, hU, hUR, -⟩ := hdata.exists_mem_nhds_frontier_subset_residual (hR t) (hfr t)
      (hint t) hDc hW (hWt t het) hzR hzW (fun u _ hzu => hzV u hzu)
      (fun s _ hzs => hzD ⟨s, hzs⟩)
    exact ⟨U, hU, fun q hq => mem_iUnion₂.mpr ⟨t, het, hUR hq⟩⟩

theorem Section34NormalPlus.splitDiskImage_boundary_subset_iUnion_residual
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34SimplexIndex 𝒦 4 → Set M₂} (hR : ∀ t, IsPLCellOn 3 (Rf t) (frontier (Rf t)))
    (hRH : ∀ t, Rf t ⊆ H t.1)
    (hDR : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34SimplexIndex 𝒦 4, frontier (Rf t) ⊆
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34SimplexIndex 𝒦 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w))
    (hio : ∀ (t : Section34SimplexIndex 𝒦 4) (a : Section34ArcIndex 𝒦 𝒦'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34VertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    section34SplitDiskImage srcBd f₁ e ⊆
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34SplitDiskImage src f₁ e := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hTfin := 𝒦.finite_simplexIndices_incident
    (Finset.card_pos.mp (by rw [e.2.2.1]; omega)) 4
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hEc : IsClosed (section34SplitDiskImage src f₁ e) := hEcell.isCompact.isClosed
  obtain ⟨w, w', hww', hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have hwe : w.1 ⊆ e.1 := by
    have h : (w.1 : Set Ea) ⊆ e.1 := by
      rw [hew]
      exact subset_union_left
    exact Finset.coe_subset.mp h
  have hw'e : w'.1 ⊆ e.1 := by
    have h : (w'.1 : Set Ea) ⊆ e.1 := by
      rw [hew]
      exact subset_union_right
    exact Finset.coe_subset.mp h
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  obtain ⟨c, hc, hVc⟩ := hdata.exists_chart_vertexBalls_of_edge e
  have hEbW : section34SplitDiskImage srcBd f₁ e ⊆
      frontier (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ w') :=
    hEcell.boundary_subset_frontier_union_in_chart (hVball w) (hVball w') hinter
      (hcut.splitDiskImage_subset_frontier hf₁ hwe) hc (hVc w hwe) (hVc w' hw'e)
  have hCovc : IsClosed (⋃ (t : Section34SimplexIndex 𝒦 4)
      (_ : Section34Incident e.1 t.1), Rf t ∩ section34SplitDiskImage src f₁ e) :=
    hTfin.isClosed_biUnion fun t _ => (hR t).isCompact.isClosed.inter hEc
  have hloc : ∀ z ∈ section34SplitDiskImage srcBd f₁ e,
      z ∈ ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34SplitDiskImage src f₁ e →
      ∃ U ∈ 𝓝 z, U ∩ section34SplitDiskImage srcBd f₁ e ⊆
        ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34SplitDiskImage src f₁ e := by
    intro z hzb hz
    obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp hz
    obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_frontier_pair_subset_iUnion_residual hdisk
      hR hRH hDR hfr hint hio h7 h9 hww' hwe hw'e hzb het hzR
    refine ⟨U, hU, fun q hq => ?_⟩
    obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp (hUR ⟨hq.1, hEbW hq.2⟩)
    exact mem_iUnion₂.mpr ⟨t', het', hqR, hEcell.boundary_subset hq.2⟩
  rcases subset_or_disjoint_of_isPreconnected_of_locally_subset
    hEcell.isConnected_boundary.isPreconnected hCovc hloc with h | h
  · exact h
  · exfalso
    obtain ⟨t, het⟩ := hcut.exists_tetrahedron_of_subdivision_face e.2.1
    obtain ⟨q, hq⟩ := (hdata.isPLCellOn_residualEdgeArc hdisk (hR t) (hDR t) (hfr t)
      (hint t) (hio t) (h7 t) het).nonempty
    exact Set.disjoint_left.mp h
      (hdata.residual_inter_splitDiskImage_subset (hR t) (hint t) (h7 t) e hq)
      (mem_iUnion₂.mpr ⟨t, het, hq⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
