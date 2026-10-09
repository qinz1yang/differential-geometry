/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ChartBigonRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonModelUpdate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34BigonSlide (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
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
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s =
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s + 2 =
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  let _ := hU
  classical
  obtain ⟨w, v, e, B, B', Bb, Dj, Jd, c, O, k, hB, hBf, hBw, hBbe, hBsplit,
    hB', hB'e, hBB', hD, hDS, hJ, hclean, hwv, hwi, hvi, hei, hinter, hc, hfc,
    hTc, hYc, hY, hDcBall, hDF, hO, hDO, hOc, hOV, hOT, hOf, hOrim, hOE, hOH,
    hforeign, hDk, hkO, hOct, hk, hki, hkS, hkY, hSfcoord, hVcoord, hTcoord,
    hEfront, hEplane⟩ := exists_section34BigonChart hh hcut hctrl hgraph hinv s hop
  obtain ⟨hfcell, -, -, -, -, -, -, hfinite, -, -⟩ := id hinv
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  have hwc : section34VertexBallImage src f₁ w ⊆ c.source :=
    subset_union_left.trans hYc
  have hDc : Dj ⊆ c.source := fun x hx =>
    hwc ((hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset (hDS hx).1)
  have hEc : section34SplitDiskImage src f₁ e ⊆ c.source := by
    rw [hinter]
    exact inter_subset_left.trans hwc
  have hEbc := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset.trans hEc
  have hfbc := (hfcell s).boundary_subset.trans hfc
  have hDSg : Dj ⊆ frontier (⋃ z, section34VertexBallImage src f₁ z) :=
    fun x hx => (hDS hx).2
  have hDB := section34Bigon_inter_faceBall_boundary hinv hB hBf hB' hB'e hBB' hD
    hDSg hJ (hclean s) hc hDc
  have hDB' := section34Bigon_inter_splitDisk_boundary hh hcut hctrl hgraph
    hBsplit hB' hB'e hD hDS hJ hc hwc
  have hEs : ∀ x ∈ (c '' section34SplitDiskImage srcBd f₁ e) ∩ k.source,
      x ∈ c '' (frontier (⋃ z, section34VertexBallImage src f₁ z) ∩ c.source) :=
    fun x hx => (hSfcoord x hx.2).mpr (hEplane x hx.2 hx.1)
  obtain ⟨Q, A, C, α, β, p, q, hQ, hDQ, -, hα, hβ, hαc, hβc,
    hpq, hAC, hp, hq, hcp, hcq, hBb, hlocal⟩ :=
    exists_section34BigonCrosscutNeighborhood hh hcut hctrl hgraph hinv s hB hB' hD
      hDB hDB' hBB' hDSg hc hfc hTc hEc hDc k hk hki hDk hSfcoord hEs
      isOpen_univ (subset_univ _)
  let S := c '' (frontier (⋃ z, section34VertexBallImage src f₁ z) ∩ c.source)
  let T := c '' section34FaceTorus (section34VertexBallImage src f₁) s
  let P := c '' fblBd s
  let E := c '' ((⋃ e', section34SplitDiskImage srcBd f₁ e') ∩ c.source)
  have hQtarget : Q ×ˢ {(0 : ℝ)} ⊆ k.target := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rcases ht with rfl
    exact (hlocal z hz).1
  have hEmem : ∀ x ∈ k.source,
      x ∈ E ↔ x ∈ c '' section34SplitDiskImage srcBd f₁ e := by
    intro x hx
    obtain ⟨y, hyO, hyx⟩ := hkO hx
    constructor
    · rintro ⟨z, ⟨hz, hzc⟩, hzx⟩
      have hzy : z = y := c.injOn hzc (hOc hyO) (hzx.trans hyx.symm)
      subst z
      obtain ⟨e', hye'⟩ := mem_iUnion.mp hz
      have he' : e' = e := by
        by_contra hne
        exact disjoint_left.mp (hOE e' hne) hyO
          ((hcut.isPLCellOn_splitDiskImage hf₁ e').boundary_subset hye')
      exact ⟨y, he' ▸ hye', hyx⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, ⟨mem_iUnion.mpr ⟨e, hz⟩, hEbc hz⟩, hzx⟩
  have hPmodel : ∀ z ∈ Q, k.symm (z, 0) ∈ P ↔ z ∈ A := by
    intro z hz
    have hzt := (hlocal z hz).1
    have hzs := k.map_target hzt
    have hsz : k.symm (z, 0) ∈ S :=
      (hSfcoord _ hzs).mpr (by rw [k.right_inv hzt])
    have htrace : k.symm (z, 0) ∈
        c '' (fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w)) ↔
        k.symm (z, 0) ∈ P := by
      constructor
      · rintro ⟨y, hy, hyz⟩
        exact ⟨y, hy.1, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        obtain ⟨x, ⟨hxS, hxc⟩, hxz⟩ := hsz
        have hxy : x = y := c.injOn hxc (hfbc hy) (hxz.trans hyz.symm)
        exact ⟨y, ⟨hy, hxy ▸ hxS⟩, hyz⟩
    exact htrace.symm.trans (hlocal z hz).2.1
  have hEmodel : ∀ z ∈ Q, k.symm (z, 0) ∈ E ↔ z ∈ C := by
    intro z hz
    exact (hEmem _ (k.map_target (hlocal z hz).1)).trans (hlocal z hz).2.2
  have hEflat : ∀ z ∈ k.target, k.symm z ∈ E → z.2 = 0 := by
    intro z hz hzE
    have hflat := hEplane _ (k.map_target hz) ((hEmem _ (k.map_target hz)).mp hzE)
    rwa [k.right_inv hz] at hflat
  have hPE : P ∩ E = c '' (fblBd s ∩ ⋃ e', section34SplitDiskImage srcBd f₁ e') := by
    change (c '' fblBd s) ∩
      (c '' ((⋃ e', section34SplitDiskImage srcBd f₁ e') ∩ c.source)) = _
    rw [← c.injOn.image_inter hfbc inter_subset_right]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hfbc hx.1⟩⟩
  have hPEfin : (P ∩ E).Finite := by
    rw [hPE]
    exact (hfinite s).image c
  obtain ⟨K, Φ, hK, hKk, hΦ, hfix, -, hΦT, hdelete, hdrop,
    G, hG, hG0, hG1, hGfix, hGK, hGT⟩ :=
    exists_chart_bigon_removal k hk hki hQ hQtarget hαc hβc hAC hpq hp hq hcp hcq
      (S := S) (Y := T) hSfcoord hTcoord hPmodel hEmodel hEflat hPEfin
  exact exists_section34BigonSlide_of_model_move hinv s hwi hvi hc hfc hTc hOc hOV hOT
    hOH hOf hOrim hforeign Φ hΦ hK (hKk.trans hkO) hfix hΦT
    G hG hG0 hG1 hGfix hGK hGT hdelete hdrop

end DifferentialGeometry.Topology.PiecewiseLinear
