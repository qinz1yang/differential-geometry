/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualEdgeCover

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

theorem Section34NormalPlus.vertexBallImage_frontier_subset_iUnion_residual
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
    (w : Section34VertexIndex 𝒦 𝒦') :
    frontier (section34VertexBallImage src f₁ w) ⊆
      (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34SplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34VertexBallImage src f₁ w := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hTfin := 𝒦.finite_simplexIndices_incident
    (Finset.card_pos.mp (by rw [w.2.2.1]; omega)) 4
  have hEfin : {e : Section34EdgeIndex 𝒦 𝒦' | w.1 ⊆ e.1}.Finite := by
    apply Set.Finite.of_finite_image
      (f := fun e : Section34EdgeIndex 𝒦 𝒦' => (⟨e.1, e.2.1⟩ : 𝒦'.complex.faces))
    · refine (𝒦'.cofaces_finite w.2.1).subset ?_
      rintro _ ⟨e, he, rfl⟩
      exact he
    · intro a _ b _ hab
      exact Subtype.ext (congrArg (fun r : 𝒦'.complex.faces => r.1) hab)
  obtain ⟨hD1, -, -, -, -, -, -, hD8, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hVball u).isCompact.isClosed
  have hEc : ∀ e, IsClosed (section34SplitDiskImage src f₁ e) := fun e =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).isCompact.isClosed
  have hCovc : IsClosed ((⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34SplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34VertexBallImage src f₁ w) :=
    (hEfin.isClosed_biUnion fun e _ => hEc e).union
      (hTfin.isClosed_biUnion fun t _ => (hR t).isCompact.isClosed.inter (hVc w))
  have hcapCov : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      ∀ q ∈ section34SplitDiskImage src f₁ e,
      q ∈ (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34SplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34VertexBallImage src f₁ w := fun e he q hq =>
    Or.inl (mem_iUnion₂.mpr ⟨e, he, hq⟩)
  have hpatchCov : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident w.1 t.1 →
      ∀ q ∈ Rf t, q ∈ section34VertexBallImage src f₁ w →
      q ∈ (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34SplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34VertexBallImage src f₁ w := fun t ht q hq hqV =>
    Or.inr (mem_iUnion₂.mpr ⟨t, ht, hq, hqV⟩)
  have hloc : ∀ z ∈ frontier (section34VertexBallImage src f₁ w),
      z ∈ (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
        section34SplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34VertexBallImage src f₁ w →
      ∃ U ∈ 𝓝 z, U ∩ frontier (section34VertexBallImage src f₁ w) ⊆
        (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
          section34SplitDiskImage src f₁ e) ∪
        ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
          Rf t ∩ section34VertexBallImage src f₁ w := by
    intro z hzS hz
    by_cases hzcap : ∃ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 ∧
        z ∈ section34SplitDiskImage src f₁ e
    · obtain ⟨e, hwe, hzE⟩ := hzcap
      obtain ⟨w', hww', hw'e, heww'⟩ : ∃ w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
          w'.1 ⊆ e.1 ∧ (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) := by
        obtain ⟨a, b, hab, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
        have hae : a.1 ⊆ e.1 := by
          have h : (a.1 : Set Ea) ⊆ e.1 := by
            rw [habe]
            exact subset_union_left
          exact Finset.coe_subset.mp h
        have hbe : b.1 ⊆ e.1 := by
          have h : (b.1 : Set Ea) ⊆ e.1 := by
            rw [habe]
            exact subset_union_right
          exact Finset.coe_subset.mp h
        rcases eq_or_eq_of_section34VertexIndex_subset e habe hwe with h | h
        · exact ⟨b, by rw [h]; exact hab, hbe, by rw [h]; exact habe⟩
        · exact ⟨a, by rw [h]; exact hab.symm, hae, by rw [h, union_comm]; exact habe⟩
      have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
      have hEcap : ∀ q ∈ frontier (section34VertexBallImage src f₁ w),
          q ∈ section34VertexBallImage src f₁ w' →
          q ∈ (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1),
            section34SplitDiskImage src f₁ e) ∪
          ⋃ (t : Section34SimplexIndex 𝒦 4) (_ : Section34Incident w.1 t.1),
            Rf t ∩ section34VertexBallImage src f₁ w := fun q hq hqw' =>
        hcapCov e hwe q (by rw [← hinter]; exact ⟨(hVc w).frontier_subset hq, hqw'⟩)
      by_cases hzb : z ∈ section34SplitDiskImage srcBd f₁ e
      · obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp
          (hdata.splitDiskImage_boundary_subset_iUnion_residual hdisk hR hRH hDR hfr hint hio h7
            h9 e hzb)
        obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_frontier_pair_subset_iUnion_residual
          hdisk hR hRH hDR hfr hint hio h7 h9 hww' hwe hw'e hzb het hzR
        refine ⟨U, hU, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34VertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp
            (hUR ⟨hq.1, mem_frontier_union_of_notMem (hVc w') hq.2 hqw'⟩)
          exact hpatchCov t' (fun x hx => het' (hwe hx)) q hqR ((hVc w).frontier_subset hq.2)
      · obtain ⟨c, hc, hVcsrc⟩ := hdata.exists_chart_vertexBalls_of_edge e
        have hends : (⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : u.1 ⊆ e.1),
            section34VertexBallImage src f₁ u) ⊆
            section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ w' := by
          refine iUnion₂_subset fun u hu => ?_
          rcases eq_or_eq_of_section34VertexIndex_subset e heww' hu with rfl | rfl
          · exact subset_union_left
          · exact subset_union_right
        have hzi : z ∈ interior (section34VertexBallImage src f₁ w ∪
            section34VertexBallImage src f₁ w') :=
          interior_mono hends
            (hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc hVcsrc ⟨hzE, hzb⟩)
        refine ⟨interior (section34VertexBallImage src f₁ w ∪
          section34VertexBallImage src f₁ w'), isOpen_interior.mem_nhds hzi, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34VertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · exfalso
          refine hq.2.2 (mem_interior.mpr
            ⟨interior (section34VertexBallImage src f₁ w ∪
              section34VertexBallImage src f₁ w') ∩
                (section34VertexBallImage src f₁ w')ᶜ, ?_,
              isOpen_interior.inter (hVc w').isOpen_compl, ⟨hq.1, hqw'⟩⟩)
          intro y hy
          exact (interior_subset hy.1).resolve_right hy.2
    · rcases hz with hz | hz
      · obtain ⟨e, he, hzE⟩ := mem_iUnion₂.mp hz
        exact absurd ⟨e, he, hzE⟩ hzcap
      · obtain ⟨t, htw, hzR, hzV⟩ := mem_iUnion₂.mp hz
        have hzV' : ∀ u, z ∈ section34VertexBallImage src f₁ u →
            section34VertexBallImage src f₁ u ⊆
              section34VertexBallImage src f₁ w := by
          intro u hzu
          by_cases huw : u = w
          · exact (congrArg (section34VertexBallImage src f₁) huw).subset
          · exfalso
            obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn huw hzu hzV
            exact hzcap ⟨e, hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzV, hze⟩
        by_cases hzD : ∃ s, z ∈ tgtD s
        · obtain ⟨s, hzs⟩ := hzD
          have hws : Section34Incident w.1 s.1 := by
            by_contra hws
            have h0 : z ∈ tgtD s ∩ section34VertexBallImage src f₁ w := ⟨hzs, hzV⟩
            rw [hD8 s w hws] at h0
            exact h0
          obtain ⟨t₁, t₂, ht12, hs1, hs2⟩ := hcut.exists_tetra_pair_of_triangle s
          have hw1 : Section34Incident w.1 t₁.1 := fun x hx =>
            convexHull_min hs1 (convex_convexHull ℝ _) (hws hx)
          have hw2 : Section34Incident w.1 t₂.1 := fun x hx =>
            convexHull_min hs2 (convex_convexHull ℝ _) (hws hx)
          have hRW := hdata.isPLCellOn_residual_union_vertexBallImage hdisk
            (hR t₁) (hRH t₁) (hDR t₁)
            (hfr t₁) (hint t₁) (hio t₁) (h7 t₁) hw1
          obtain ⟨c₁, hc₁, hHc₁, hVc₁, -⟩ := hdata.exists_chart_tetrahedron t₁
          have hRWc : Rf t₁ ∪ section34VertexBallImage src f₁ w ⊆ c₁.source :=
            union_subset ((hRH t₁).trans hHc₁) (hVc₁ w hw1)
          obtain ⟨U, hU, hUR⟩ := hdata.exists_mem_nhds_frontier_subset_union hdisk hR hDR hfr
            hint h7 h9 ht12 hs1 hs2 (subset_iUnion₂_of_subset w hw2 subset_rfl) hRW hc₁ hRWc
            hzs hzV'
          refine ⟨U, hU, fun q hq => ?_⟩
          rcases hUR hq with h | h
          · exact hpatchCov t₁ hw1 q h ((hVc w).frontier_subset hq.2)
          · exact hpatchCov t₂ hw2 q h ((hVc w).frontier_subset hq.2)
        · obtain ⟨U, hU, hUR, -⟩ := hdata.exists_mem_nhds_frontier_subset_residual (hR t)
            (hfr t) (hint t) hDc (hVball w) (subset_iUnion₂_of_subset w htw subset_rfl) hzR hzS
            (fun u _ hzu => hzV' u hzu) (fun s _ hzs => hzD ⟨s, hzs⟩)
          exact ⟨U, hU, fun q hq =>
            hpatchCov t htw q (hUR hq) ((hVc w).frontier_subset hq.2)⟩
  rcases subset_or_disjoint_of_isPreconnected_of_locally_subset
    (hVball w).isConnected_boundary.isPreconnected hCovc hloc with h | h
  · exact h
  · exfalso
    obtain ⟨e, he⟩ := hcut.exists_edgeIndex_of_vertex w
    obtain ⟨q, hq⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
    exact Set.disjoint_left.mp h (hcut.splitDiskImage_subset_frontier hf₁ he hq)
      (hcapCov e he q hq)

end DifferentialGeometry.Topology.PiecewiseLinear
