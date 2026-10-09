/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.SubsetImage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonInvariantUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonSupport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPlaneChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34BigonChart (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd s) :
    ∃ (w v : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (B B' Bb Dj Jd : Set M₂) (c : OpenPartialHomeomorph M₂ E3) (O : Set M₂)
      (k : OpenPartialHomeomorph E3 (Plane × ℝ)),
      IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ section34VertexBallImage srcBd f₁ w ∧
      Bb ⊆ section34SplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ e', section34SplitDiskImage src f₁ e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ section34SplitDiskImage srcBd f₁ e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧
      Dj ⊆ section34VertexBallImage srcBd f₁ w ∩
        frontier (⋃ z, section34VertexBallImage src f₁ z) ∧ Jd = B ∪ B' ∧
      (∀ s', Disjoint (Dj \ Jd) (fblBd s')) ∧
      w ≠ v ∧ Section34Incident w.1 s.1 ∧ Section34Incident v.1 s.1 ∧
      Section34Incident e.1 s.1 ∧
      section34SplitDiskImage src f₁ e =
        section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ v ∧
      c ∈ (plGroupoid 3).maximalAtlas M₂ ∧ fbl s ⊆ c.source ∧
      section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source ∧
      section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v ⊆ c.source ∧
      IsPLBall 3 (c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v)) ∧ IsPLBall 2 (c '' Dj) ∧
      c '' Dj ⊆ frontier (c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v)) ∧
      IsOpen O ∧ Dj ⊆ O ∧ O ⊆ c.source ∧
      O ∩ (⋃ z, section34VertexBallImage src f₁ z) =
        O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) ∧
      O ∩ section34FaceTorus (section34VertexBallImage src f₁) s =
        O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) ∧
      Disjoint O (⋃ s' ≠ s, fbl s') ∧ Disjoint O (h '' simplexRim 𝒦 s.1) ∧
      (∀ e', e' ≠ e → Disjoint O (section34SplitDiskImage src f₁ e')) ∧
      (∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
        O ⊆ interior (H t.1)) ∧
      (∀ z : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident z.1 s.1 →
        Disjoint O (section34VertexBallImage src f₁ z)) ∧
      c '' Dj ⊆ k.source ∧ k.source ⊆ c '' O ∧ c '' O ⊆ c.target ∧
      IsPiecewiseAffineOn k k.source ∧ IsPiecewiseAffineOn k.symm k.target ∧
      (∀ x ∈ k.source, x ∈ frontier (c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v)) ↔ (k x).2 = 0) ∧
      (∀ x ∈ k.source, x ∈ c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v) ↔ 0 ≤ (k x).2) ∧
      (∀ x ∈ k.source, x ∈ c '' (frontier (⋃ z, section34VertexBallImage src f₁ z) ∩
        c.source) ↔ (k x).2 = 0) ∧
      (∀ x ∈ k.source, x ∈ c '' ((⋃ z, section34VertexBallImage src f₁ z) ∩
        c.source) ↔ 0 ≤ (k x).2) ∧
      (∀ x ∈ k.source, x ∈ c '' section34FaceTorus (section34VertexBallImage src f₁) s ↔
        0 ≤ (k x).2) ∧
      c '' section34SplitDiskImage srcBd f₁ e ⊆
        frontier (c '' (section34VertexBallImage src f₁ w ∪
          section34VertexBallImage src f₁ v)) ∧
      (∀ x ∈ k.source, x ∈ c '' section34SplitDiskImage srcBd f₁ e → (k x).2 = 0) := by
  obtain ⟨w, v, e, B, B', Bb, Dj, Jd, c, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean, hwv, hwi, hvi, hei, hinter, hc, hfc, hTc, hYc, hY,
    hDcBall, hDF⟩ := exists_section34BigonBall hh hcut hctrl hgraph hinv s hop
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  have hWcell := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁ v
  have hwc : section34VertexBallImage src f₁ w ⊆ c.source :=
    subset_union_left.trans hYc
  have hvc : section34VertexBallImage src f₁ v ⊆ c.source :=
    subset_union_right.trans hYc
  have hDw : Dj ⊆ section34VertexBallImage src f₁ w := fun x hx =>
    hWcell.boundary_subset (hDS hx).1
  have hDc : Dj ⊆ c.source := hDw.trans hwc
  have hDSg : Dj ⊆ frontier (⋃ z, section34VertexBallImage src f₁ z) :=
    fun x hx => (hDS hx).2
  obtain ⟨O₁, hO₁, hDO₁, hO₁c, hO₁V, hO₁T, hO₁E⟩ :=
    exists_section34BigonCarrier hh hcut hctrl hgraph hwv hwi hvi hinter hc hwc
      hD hDS hJ hBbe hBsplit hB'e
  have havoid : ∀ s', s' ≠ s → Disjoint Dj (fbl s') := by
    intro s' hs'
    exact section34Bigon_disjoint_other_faceBall hinv (Ne.symm hs') hB hBf hB' hB'e
      hBB' hD hDSg hJ (hclean s') hc hDc
  obtain ⟨O₂, hO₂, hDO₂, hO₂f, hO₂rim⟩ :=
    exists_isOpen_section34BigonSupport hh hcut hctrl hgraph hinv s w hDw hDSg havoid
  obtain ⟨O₃, hO₃, hDO₃, hO₃H⟩ :=
    exists_isOpen_section34BigonCarrierInterior hh hcut hctrl hgraph hwi hDw
  let O := O₁ ∩ (O₂ ∩ O₃)
  have hO : IsOpen O := hO₁.inter (hO₂.inter hO₃)
  have hDO : Dj ⊆ O := fun x hx => ⟨hDO₁ hx, hDO₂ hx, hDO₃ hx⟩
  have hOc : O ⊆ c.source := fun _ hx => hO₁c hx.1
  have hrestrict : ∀ A A' : Set M₂, O₁ ∩ A = O₁ ∩ A' → O ∩ A = O ∩ A' := by
    intro A A' hAA'
    ext x
    exact ⟨fun hx => ⟨hx.1, ((Set.ext_iff.mp hAA' x).mp ⟨hx.1.1, hx.2⟩).2⟩,
      fun hx => ⟨hx.1, ((Set.ext_iff.mp hAA' x).mpr ⟨hx.1.1, hx.2⟩).2⟩⟩
  have hOV := hrestrict _ _ hO₁V
  have hOT := hrestrict _ _ hO₁T
  have hOf : Disjoint O (⋃ s' ≠ s, fbl s') := hO₂f.mono_left (fun _ hx => hx.2.1)
  have hOrim : Disjoint O (h '' simplexRim 𝒦 s.1) :=
    hO₂rim.mono_left (fun _ hx => hx.2.1)
  have hOE : ∀ e', e' ≠ e → Disjoint O (section34SplitDiskImage src f₁ e') :=
    fun e' he' => (hO₁E e' he').mono_left inter_subset_left
  have hOH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      O ⊆ interior (H t.1) := fun t ht _ hx => hO₃H t ht hx.2.2
  have hforeign := hcut.disjoint_vertexBallImage_of_nonincident_of_local_pair hgraph
    hwi hvi hei hOV hOE
  obtain ⟨k, hDk, hkO, hk, hki, hkS, hkY⟩ :=
    hY.exists_openPartialHomeomorph_boundary_disk_plane hDcBall hDF
      (c.isOpen_image_of_subset_source hO hOc) (image_mono hDO)
  have hOct : c '' O ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hOc hx)
  let Y := section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v
  have hYcompact : IsCompact Y := hWcell.isCompact.union hVcell.isCompact
  have hfront : c '' frontier Y = frontier (c '' Y) :=
    c.image_frontier_of_isCompact hYcompact hYc
  have hfrontc : frontier Y ⊆ c.source := hYcompact.isClosed.frontier_subset.trans hYc
  have hlocalfront : frontier (⋃ z, section34VertexBallImage src f₁ z) ∩ O =
      frontier Y ∩ O := by
    have heq : (⋃ z, section34VertexBallImage src f₁ z) ∩ O = Y ∩ O :=
      (inter_comm _ _).trans (hOV.trans (inter_comm _ _))
    calc
      _ = frontier ((⋃ z, section34VertexBallImage src f₁ z) ∩ O) ∩ O :=
        (frontier_inter_open_inter hO).symm
      _ = frontier (Y ∩ O) ∩ O := by rw [heq]
      _ = _ := frontier_inter_open_inter hO
  have hmem (A : Set M₂) (x : M₂) (hx : x ∈ c.source) :
      c x ∈ c '' (A ∩ c.source) ↔ x ∈ A := by
    rw [c.injOn.mem_image_iff inter_subset_right hx]
    exact and_iff_left hx
  have hSfcoord : ∀ x ∈ k.source,
      x ∈ c '' (frontier (⋃ z, section34VertexBallImage src f₁ z) ∩ c.source) ↔
        (k x).2 = 0 := by
    intro z hz
    obtain ⟨x, hxO, rfl⟩ := hkO hz
    rw [hmem _ x (hOc hxO), ← hkS _ hz, ← hfront,
      c.injOn.mem_image_iff hfrontc (hOc hxO)]
    exact ⟨fun hx => ((Set.ext_iff.mp hlocalfront x).mp ⟨hx, hxO⟩).1,
      fun hx => ((Set.ext_iff.mp hlocalfront x).mpr ⟨hx, hxO⟩).1⟩
  have hVcoord : ∀ x ∈ k.source,
      x ∈ c '' ((⋃ z, section34VertexBallImage src f₁ z) ∩ c.source) ↔ 0 ≤ (k x).2 := by
    intro z hz
    obtain ⟨x, hxO, rfl⟩ := hkO hz
    rw [hmem _ x (hOc hxO), ← hkY _ hz, c.injOn.mem_image_iff hYc (hOc hxO)]
    exact ⟨fun hx => ((Set.ext_iff.mp hOV x).mp ⟨hxO, hx⟩).2,
      fun hx => ((Set.ext_iff.mp hOV x).mpr ⟨hxO, hx⟩).2⟩
  have hTcoord : ∀ x ∈ k.source,
      x ∈ c '' section34FaceTorus (section34VertexBallImage src f₁) s ↔ 0 ≤ (k x).2 := by
    intro z hz
    obtain ⟨x, hxO, rfl⟩ := hkO hz
    rw [c.injOn.mem_image_iff hTc (hOc hxO), ← hkY _ hz,
      c.injOn.mem_image_iff hYc (hOc hxO)]
    exact ⟨fun hx => ((Set.ext_iff.mp hOT x).mp ⟨hxO, hx⟩).2,
      fun hx => ((Set.ext_iff.mp hOT x).mpr ⟨hxO, hx⟩).2⟩
  have hEc : section34SplitDiskImage src f₁ e ⊆ c.source :=
    fun x hx => hwc (hinter ▸ hx).1
  obtain ⟨q, hq, hqb⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_image_chart hc hEc
  have hEcell : IsPLCellOn 2 (c '' section34SplitDiskImage src f₁ e)
      (c '' section34SplitDiskImage srcBd f₁ e) :=
    hqb.symm ▸ isPLCellOn_id_of_isPLBall hq
  have hEwsrc : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    intro x hx
    have hfx : f₁ x ∈ section34VertexBallImage src f₁ w :=
      (hinter ▸ (show f₁ x ∈ section34SplitDiskImage src f₁ e from
        mem_image_of_mem f₁ hx)).1
    obtain ⟨y, hy, hyx⟩ := hfx
    exact hf₁.injOn (subset_iUnion (fun z => src (.vertexBall z)) w hy)
      (hcut.splitDisk_subset_cutNeighborhood e hx) hyx ▸ hy
  have hEw : section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage srcBd f₁ w := by
    refine image_mono fun x hx => ?_
    rw [hcut.2.2.2.2.1 (.vertexBall w)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hEwsrc, by simp⟩, hx⟩
  obtain ⟨hW, hWbd⟩ := hWcell.isPLBall_image_chart hc hwc
  obtain ⟨hV, -⟩ := hVcell.isPLBall_image_chart hc hvc
  have hci : c '' section34VertexBallImage src f₁ w ∩
      c '' section34VertexBallImage src f₁ v = c '' section34SplitDiskImage src f₁ e := by
    rw [hinter]
    exact (c.injOn.image_inter hwc hvc).symm
  have hEfront : c '' section34SplitDiskImage srcBd f₁ e ⊆ frontier (c '' Y) := by
    rw [image_union]
    exact boundary_subset_frontier_union_of_inter_eq hW hV hEcell hci
      (hWbd ▸ image_mono hEw)
  refine ⟨w, v, e, B, B', Bb, Dj, Jd, c, O, k, hB, hBf, hBw, hBbe, hBsplit,
    hB', hB'e, hBB', hD, hDS, hJ, hclean, hwv, hwi, hvi, hei, hinter, hc, hfc,
    hTc, hYc, hY, hDcBall, hDF, hO, hDO, hOc, hOV, hOT, hOf, hOrim, hOE, hOH,
    hforeign, hDk, hkO, hOct, hk, hki, hkS, hkY, hSfcoord, hVcoord, hTcoord, hEfront, ?_⟩
  exact fun x hx hxe => (hkS x hx).mp (hEfront hxe)

end DifferentialGeometry.Topology.PiecewiseLinear
