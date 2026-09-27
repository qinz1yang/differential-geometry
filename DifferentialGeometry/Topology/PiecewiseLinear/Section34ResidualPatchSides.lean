/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPatch
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellChartBoundary

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

theorem Section34NormalPlus.residual_inter_vertexBallImage_eq_of_sides
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
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : Section34Incident w.1 t.1) {m : ℕ}
    {sK : Fin (m + 2) → Section34SimplexIndex 𝒦 3}
    {eK : Fin (m + 2) → Section34EdgeIndex 𝒦 𝒦'}
    (hwsK : ∀ k, Section34Incident w.1 (sK k).1) (hweK : ∀ k, w.1 ⊆ (eK k).1)
    (heKt : ∀ k, Section34Incident (eK k).1 t.1)
    (hscomp : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    {A Ab B Bb : Set M₂} (hqA : IsPLCellOn 2 A Ab) (hqB : IsPLCellOn 2 B Bb)
    (hAB : A ∪ B ∪ (⋃ k, section34SplitDiskImage src f₁ (eK k)) =
      frontier (section34VertexBallImage src f₁ w))
    (hABi : A ∩ B = ⋃ k, tgtA ⟨(sK k, w), hwsK k⟩)
    (hH : ∀ k, A ∩ section34SplitDiskImage src f₁ (eK k) ∪
      B ∩ section34SplitDiskImage src f₁ (eK k) =
        section34SplitDiskImage srcBd f₁ (eK k))
    (hqBb : Bb = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, B ∩ section34SplitDiskImage src f₁ (eK k))
    (hAR : A \ Ab ⊆ R)
    (hBR : Disjoint (B \ Bb) R) :
    R ∩ section34VertexBallImage src f₁ w = A ∧
      ∀ k, R ∩ section34SplitDiskImage src f₁ (eK k) =
        A ∩ section34SplitDiskImage src f₁ (eK k) := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hRc : IsClosed R := hR.isCompact.isClosed
  have hVball : ∀ u, IsPLCellOn 3 (section34VertexBallImage src f₁ u)
      (frontier (section34VertexBallImage src f₁ u)) := by
    intro u
    have hu := hcut.isPLCellOn_vertexBallImage hf₁ u
    rwa [hu.boundary_eq_frontier] at hu
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hVball u).isCompact.isClosed
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hAR' : A ⊆ R := fun z hz => closure_minimal hAR hRc
    (hqA.closure_sdiff_boundary.symm.subset hz)
  have hAS : A ⊆ frontier (section34VertexBallImage src f₁ w) := fun z hz =>
    hAB.subset (Or.inl (Or.inl hz))
  have hBS : B ⊆ frontier (section34VertexBallImage src f₁ w) := fun z hz =>
    hAB.subset (Or.inl (Or.inr hz))
  have hArun : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ A := fun k z hz =>
    (hABi.symm.subset (mem_iUnion.mpr ⟨k, hz⟩)).1
  have hBEA : ∀ k, ∀ y ∈ R, y ∈ B ∩ section34SplitDiskImage src f₁ (eK k) → y ∈ A := by
    intro k y hyR hyBE
    by_contra hyA
    obtain ⟨a, b, hab, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn (eK k)
    have hae : a.1 ⊆ (eK k).1 := by
      have h : (a.1 : Set Ea) ⊆ (eK k).1 := by
        rw [habe]
        exact subset_union_left
      exact Finset.coe_subset.mp h
    have hbe : b.1 ⊆ (eK k).1 := by
      have h : (b.1 : Set Ea) ⊆ (eK k).1 := by
        rw [habe]
        exact subset_union_right
      exact Finset.coe_subset.mp h
    obtain ⟨w', hww', hw'e⟩ : ∃ w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
        w'.1 ⊆ (eK k).1 := by
      rcases eq_or_eq_of_section34VertexIndex_subset (eK k) habe (hweK k) with h | h
      · exact ⟨b, by rw [h]; exact hab, hbe⟩
      · exact ⟨a, by rw [h]; exact hab.symm, hae⟩
    have hw't : Section34Incident w'.1 t.1 := fun z hz => heKt k (hw'e hz)
    have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' (hweK k) hw'e
    obtain ⟨c, hc, -, hVcsrc, -⟩ := hdata.exists_chart_tetrahedron t
    have hE := hcut.isPLCellOn_splitDiskImage hf₁ (eK k)
    have hW := (hVball w).union_of_inter_eq_of_subset_frontier_in_chart (hVball w') hE
      hinter (hcut.splitDiskImage_subset_frontier hf₁ hw'e)
      hc (hVcsrc w hw) (hVcsrc w' hw't)
    have hyEb := hdata.residual_inter_splitDiskImage_subset hR hint h7 (eK k) ⟨hyR, hyBE.2⟩
    have hyW : y ∈ frontier (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ w') :=
      hE.boundary_subset_frontier_union_in_chart (hVball w) (hVball w') hinter
        (hcut.splitDiskImage_subset_frontier hf₁ (hweK k))
        hc (hVcsrc w hw) (hVcsrc w' hw't) hyEb
    have hyww' : y ∈ section34VertexBallImage src f₁ w ∩
        section34VertexBallImage src f₁ w' := by
      rw [hinter]
      exact hyBE.2
    obtain ⟨U, hU, hUR, -⟩ := hdata.exists_mem_nhds_frontier_subset_residual hR hfr hint hDc
      hW (union_subset (subset_iUnion₂_of_subset w hw subset_rfl)
        (subset_iUnion₂_of_subset w' hw't subset_rfl)) hyR hyW
      (fun u _ hyu => by
        by_cases huw : u = w
        · rw [huw]
          exact subset_union_left
        · by_cases huw' : u = w'
          · rw [huw']
            exact subset_union_right
          · have h0 : y ∈ section34VertexBallImage src f₁ u ∩
                section34VertexBallImage src f₁ w ∩
                section34VertexBallImage src f₁ w' := ⟨⟨hyu, hyww'.1⟩, hyww'.2⟩
            rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁.injOn huw huw' hww'] at h0
            exact h0.elim)
      (fun s hs hys => by
        have hse : Section34Incident (eK k).1 s.1 := by
          by_contra hse
          have h0 : y ∈ tgtD s ∩ section34SplitDiskImage src f₁ (eK k) := ⟨hys, hyBE.2⟩
          rw [hdisk.faceDisk_inter_splitDisk_eq_empty hdata hse] at h0
          exact h0
        have hws : Section34Incident w.1 s.1 := fun z hz => hse (hweK k hz)
        obtain ⟨j, rfl⟩ := hscomp s hs hws
        exact hyA (hArun j ((hdisk.faceDisk_inter_vertexBall_eq ⟨(sK j, w), hwsK j⟩).subset
          ⟨hys, hyww'.1⟩)))
    have hyB : y ∈ closure (B \ Bb) := by
      rw [hqB.closure_sdiff_boundary]
      exact hyBE.1
    obtain ⟨q, hqU, hqB'⟩ := mem_closure_iff_nhds.mp hyB U hU
    have hqS : q ∈ frontier (section34VertexBallImage src f₁ w) := hBS hqB'.1
    have hqw' : q ∉ section34VertexBallImage src f₁ w' := fun hq => hqB'.2 (by
      rw [hqBb]
      refine Or.inr (mem_iUnion.mpr ⟨k, hqB'.1, ?_⟩)
      rw [← hinter]
      exact ⟨(hVc w).frontier_subset hqS, hq⟩)
    exact Set.disjoint_left.mp hBR hqB'
      (hUR ⟨hqU, mem_frontier_union_of_notMem (hVc w') hqS hqw'⟩)
  have hRE : ∀ k, R ∩ section34SplitDiskImage src f₁ (eK k) =
      A ∩ section34SplitDiskImage src f₁ (eK k) := by
    intro k
    apply Subset.antisymm
    · intro y hy
      have hyEb := hdata.residual_inter_splitDiskImage_subset hR hint h7 (eK k) hy
      rw [← hH k] at hyEb
      rcases hyEb with hyA | hyB
      · exact hyA
      · exact ⟨hBEA k y hy.1 hyB, hy.2⟩
    · exact fun y hy => ⟨hAR' hy.1, hy.2⟩
  refine ⟨Subset.antisymm ?_ fun y hy => ⟨hAR' hy, (hVc w).frontier_subset (hAS hy)⟩, hRE⟩
  intro y hy
  have hyS := hR.inter_subset_frontier_of_disjoint_interior_left
    (hint.mono_right (subset_iUnion₂_of_subset w hw subset_rfl)) hy
  rw [← hAB] at hyS
  rcases hyS with (hyA | hyB) | hyE
  · exact hyA
  · by_cases hyb : y ∈ Bb
    · rw [hqBb] at hyb
      rcases hyb with hyr | hyBE
      · rw [← hABi] at hyr
        exact hyr.1
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hyBE
        exact hBEA k y hy.1 hk
    · exact absurd hy.1 (Set.disjoint_left.mp hBR ⟨hyB, hyb⟩)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hyE
    have h0 : y ∈ R ∩ section34SplitDiskImage src f₁ (eK k) := ⟨hy.1, hk⟩
    rw [hRE k] at h0
    exact h0.1

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.residual_sides
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {w : Section34VertexIndex 𝒦 𝒦'} {m : ℕ}
    {sK : Fin (m + 2) → Section34SimplexIndex 𝒦 3}
    {eK : Fin (m + 2) → Section34EdgeIndex 𝒦 𝒦'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hsinj : Function.Injective sK)
    (hscomp : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    (hecomp : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k)
    {X Xb Y Yb : Set M₂} (hqX : IsPLCellOn 2 X Xb) (hqY : IsPLCellOn 2 Y Yb)
    (hXY : X ∪ Y ∪ (⋃ k, section34SplitDiskImage src f₁ (eK k)) =
      frontier (section34VertexBallImage src f₁ w))
    (hqXb : Xb = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, X ∩ section34SplitDiskImage src f₁ (eK k))
    (hqYb : Yb = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, Y ∩ section34SplitDiskImage src f₁ (eK k)) :
    (X \ Xb ⊆ R ∧ Disjoint (Y \ Yb) R) ∨
      (Y \ Yb ⊆ R ∧ Disjoint (X \ Xb) R) := by
  have hw : Section34Incident w.1 t.1 := fun z hz =>
    convexHull_min (hsK 0) (convex_convexHull ℝ _) (hwsK 0 hz)
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hRc : IsClosed R := hR.isCompact.isClosed
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hEc : ∀ e, IsClosed (section34SplitDiskImage src f₁ e) := fun e =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).isCompact.isClosed
  obtain ⟨hD1, -, -, -, hD5, hA6, -, hD8, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hAc : ∀ a, IsClosed (tgtA a) := fun a => (hA6 a).isCompact.isClosed
  have hrD : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ tgtD (sK k) := fun k z hz =>
    ((hdisk.faceDisk_inter_vertexBall_eq ⟨(sK k, w), hwsK k⟩).symm.subset hz).1
  have hgen : ∀ (Z Zb : Set M₂),
      Z ⊆ frontier (section34VertexBallImage src f₁ w) →
      Zb = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, Z ∩ section34SplitDiskImage src f₁ (eK k) →
      ∀ y ∈ Z \ Zb, y ∈ R →
        ∃ U ∈ 𝓝 y, U ∩ (Z \ Zb) ⊆ R := by
    intro Z Zb hZS hqZb y hy hyR
    have hyS := hZS hy.1
    have hyV := (hVc w).frontier_subset hyS
    obtain ⟨U, hU, hUR, -⟩ := hdata.exists_mem_nhds_frontier_subset_residual hR hfr hint hDc
      (by
        have hwc := hcut.isPLCellOn_vertexBallImage hf₁ w
        rwa [hwc.boundary_eq_frontier] at hwc)
      (subset_iUnion₂_of_subset w hw subset_rfl) hyR hyS
      (fun u _ hyu => by
        by_cases huw : u = w
        · exact (congrArg (section34VertexBallImage src f₁) huw).subset
        · exfalso
          obtain ⟨e, hye⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn huw hyu hyV
          have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hye hyV
          by_cases het : Section34Incident e.1 t.1
          · obtain ⟨l, rfl⟩ := hecomp e het hwe
            exact hy.2 (by
              rw [hqZb]
              exact Or.inr (mem_iUnion.mpr ⟨l, hy.1, hye⟩))
          · have h0 : y ∈ R ∩ section34SplitDiskImage src f₁ e := ⟨hyR, hye⟩
            rw [hcut.residual_inter_splitDiskImage_eq_empty hf₁.injOn h7 het] at h0
            exact h0)
      (fun s hs hys => by
        have hws : Section34Incident w.1 s.1 := by
          by_contra hws
          have h0 : y ∈ tgtD s ∩ section34VertexBallImage src f₁ w := ⟨hys, hyV⟩
          rw [hD8 s w hws] at h0
          exact h0
        obtain ⟨j, rfl⟩ := hscomp s hs hws
        exact hy.2 (by
          rw [hqZb]
          exact Or.inl (mem_iUnion.mpr ⟨j, (hdisk.faceDisk_inter_vertexBall_eq
            ⟨(sK j, w), hwsK j⟩).subset ⟨hys, hyV⟩⟩)))
    exact ⟨U, hU, fun z hz => hUR ⟨hz.1, hZS hz.2.1⟩⟩
  have hXS : X ⊆ frontier (section34VertexBallImage src f₁ w) := fun z hz =>
    hXY.subset (Or.inl (Or.inl hz))
  have hYS : Y ⊆ frontier (section34VertexBallImage src f₁ w) := fun z hz =>
    hXY.subset (Or.inl (Or.inr hz))
  have hXo : X \ Xb ⊆ R ∨
      Disjoint (X \ Xb) R :=
    subset_or_disjoint_of_isPreconnected_of_locally_subset
      (hqX.isConnected_of_sdiff_subset subset_rfl sdiff_subset).isPreconnected hRc
      (hgen X Xb hXS hqXb)
  have hYo : Y \ Yb ⊆ R ∨
      Disjoint (Y \ Yb) R :=
    subset_or_disjoint_of_isPreconnected_of_locally_subset
      (hqY.isConnected_of_sdiff_subset subset_rfl sdiff_subset).isPreconnected hRc
      (hgen Y Yb hYS hqYb)
  obtain ⟨y₀, hy₀A, hy₀E⟩ := hdisk.exists_mem_faceArc_notMem_splitDisk ⟨(sK 0, w), hwsK 0⟩
  have hFc : IsClosed ((⋃ k, section34SplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩) :=
    (isClosed_iUnion_of_finite fun k => hEc (eK k)).union
      (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hAc _)
  have hy₀F : y₀ ∉ (⋃ k, section34SplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩ := by
    rintro (hy | hy)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      exact hy₀E (eK k) hk
    · obtain ⟨k, hk0, hk⟩ := mem_iUnion₂.mp hy
      exact Set.disjoint_left.mp (hD5 (sK 0) (sK k) (hsinj.ne (Ne.symm hk0))) (hrD 0 hy₀A)
        (hrD k hk)
  obtain ⟨⟨z, hzU, hzS, hzR, hzD⟩, z', hz'U, hz'S, hz'R⟩ :=
    hio ⟨(sK 0, w), hwsK 0⟩ (hsK 0) y₀ hy₀A hy₀E _ (hFc.isOpen_compl.mem_nhds hy₀F)
  have hclass : ∀ x ∈ ((⋃ k, section34SplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩)ᶜ,
      x ∈ frontier (section34VertexBallImage src f₁ w) → x ∉ tgtD (sK 0) →
      x ∈ X \ Xb ∨ x ∈ Y \ Yb := by
    intro x hxF hxS hxD
    have hxE : ∀ k, x ∉ section34SplitDiskImage src f₁ (eK k) := fun k hk =>
      hxF (Or.inl (mem_iUnion.mpr ⟨k, hk⟩))
    have hxr : ∀ k, x ∉ tgtA ⟨(sK k, w), hwsK k⟩ := fun k hk => by
      by_cases hk0 : k = 0
      · subst hk0
        exact hxD (hrD 0 hk)
      · exact hxF (Or.inr (mem_iUnion₂.mpr ⟨k, hk0, hk⟩))
    rw [← hXY] at hxS
    rcases hxS with (hxX | hxY) | hxE'
    · refine Or.inl ⟨hxX, fun hb => ?_⟩
      rw [hqXb] at hb
      rcases hb with hb | hb
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxr k hk
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxE k hk.2
    · refine Or.inr ⟨hxY, fun hb => ?_⟩
      rw [hqYb] at hb
      rcases hb with hb | hb
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxr k hk
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxE k hk.2
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hxE'
      exact absurd hk (hxE k)
  have hz'D : z' ∉ tgtD (sK 0) := fun h =>
    hz'R (hRc.frontier_subset (hDR (sK 0) (hsK 0) h))
  rcases hclass z hzU hzS hzD with hzX | hzY
  · rcases hXo with hXR | hXR
    · rcases hclass z' hz'U hz'S hz'D with hz'X | hz'Y
      · exact absurd (hXR hz'X) hz'R
      · rcases hYo with hYR | hYR
        · exact absurd (hYR hz'Y) hz'R
        · exact Or.inl ⟨hXR, hYR⟩
    · exact absurd hzR (Set.disjoint_left.mp hXR hzX)
  · rcases hYo with hYR | hYR
    · rcases hclass z' hz'U hz'S hz'D with hz'X | hz'Y
      · rcases hXo with hXR | hXR
        · exact absurd (hXR hz'X) hz'R
        · exact Or.inr ⟨hYR, hXR⟩
      · exact absurd (hYR hz'Y) hz'R
    · exact absurd hzR (Set.disjoint_left.mp hYR hzY)

end DifferentialGeometry.Topology.PiecewiseLinear
