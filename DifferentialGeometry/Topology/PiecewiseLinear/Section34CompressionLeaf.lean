/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionInside
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionCases
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutsideTube

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Disjoint

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34Compression_of_disjoint
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {w : Section34VertexIndex 𝒦 𝒦'} {Dj Jd : Set M₂}
    (hDcell : IsPLCellOn 2 Dj Jd) (hDw : Dj ⊆ section34VertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd)
    (hDE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (section34SplitDiskImage src f₁ e))
    (hDo : ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s'))
    (hout : Disjoint (Dj \ Jd) (fbl s)) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨-, -, hfV, -, -, -, -, -, -, hext⟩ := id hinv
  obtain ⟨t₀, hst₀, c, hc, hHc, hfsc, hTc, hTcomp, O₀, hO₀def, hO₀, hfO₀, hSgO₀⟩ :=
    exists_chart_section34FaceBall_tetra hh hcut hctrl hgraph hext s (hfV s)
  by_cases hclean : ∀ Y : Set M₂, IsPLCellOn 3 Y (frontier Y) → frontier Y ⊆ Dj ∪ fblBd s →
      Disjoint (interior (fbl s)) Y → Y ⊆ interior (H t₀.1) →
      Disjoint (interior Y) (frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) ∧
      ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
        Disjoint Y (section34VertexBallImage src f₁ u)
  · exact exists_section34Compression_of_disjoint_of_cleanPocket hh hcut hctrl hgraph hinv s
      hDcell hDw hDJ hDE hDo hout t₀ hst₀ hc hHc hfsc hTc hTcomp hO₀def hO₀ hfO₀ hSgO₀ hclean
  · obtain ⟨Y, hY⟩ := not_forall.mp hclean
    obtain ⟨hYcell, hY⟩ := Classical.not_imp.mp hY
    obtain ⟨hYfr, hY⟩ := Classical.not_imp.mp hY
    obtain ⟨hYP, hY⟩ := Classical.not_imp.mp hY
    obtain ⟨hYH, hY⟩ := Classical.not_imp.mp hY
    exact exists_section34Compression_of_disjoint_of_uncleanPocket hh hcut hctrl hgraph hinv s
      hDcell hDw hDJ hDE hDo hout t₀ hst₀ hc hHc hfsc hTc hTcomp hO₀def hO₀ hfO₀ hSgO₀ hYcell
      hYfr hYP hYH hY

end Disjoint

section Leaf

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34Compression (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  let _ := hU
  classical
  obtain ⟨w, Dj, Jd, hDcell, hDw, hJdb, hDJ, hDE, hDo⟩ := hop
  obtain ⟨hfcell, -, hfV, -, -, -, -, -, -, hext⟩ := id hinv
  obtain ⟨-, -, -, hcell, -⟩ := id hcut
  obtain ⟨t₀, -, c, hc, -, hfsc, hTc, -⟩ :=
    exists_chart_section34FaceBall_tetra hh hcut hctrl hgraph hext s (hfV s)
  have hfbs : fblBd s ⊆ fbl s := (hfcell s).boundary_subset
  have hJdD : Jd ⊆ Dj := hDcell.boundary_subset
  obtain ⟨yJ, hyJ⟩ : Jd.Nonempty := by
    obtain ⟨P0, r0, u0, -, -, -, hB⟩ := id hDcell
    rw [hB]
    exact ⟨u0 (r0 (Pi.single 0 1)), r0 (Pi.single 0 1),
      ⟨Pi.single 0 1, ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, 1,
        Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide) (1 : ℝ)⟩, rfl⟩, rfl⟩
  have hDwV : Dj ⊆ section34VertexBallImage src f₁ w := fun z hz =>
    image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)
  have hwinc : Section34Incident w.1 s.1 := by
    by_contra hn
    have hmem : yJ ∈ fbl s ∩ section34VertexBallImage src f₁ w :=
      ⟨hfbs (hJdb hyJ), hDwV (hJdD hyJ)⟩
    rw [hfV s w hn] at hmem
    exact hmem
  have hDjc : Dj ⊆ c.source := fun z hz =>
    hTc (mem_iUnion₂.mpr ⟨⟨(s, w), hwinc⟩, rfl, hDwV hz⟩)
  have hDF : Dj ∩ fblBd s ⊆ Jd := hDJ.subset
  rcases subset_interior_or_disjoint_sdiff_of_isPLCellOn hc (hfcell s) hDcell hfsc hDjc hDF with
    hin | hout
  · refine exists_section34Compression_of_subset hh hcut hctrl hgraph hinv s hDcell hDw hDJ hDE
      fun z hz => ?_
    by_cases hzJ : z ∈ Jd
    · exact hfbs (hJdb hzJ)
    · exact interior_subset (hin ⟨hz, hzJ⟩)
  · exact exists_section34Compression_of_disjoint hh hcut hctrl hgraph hinv s hDcell hDw hDJ hDE
      hDo hout

end Leaf

end DifferentialGeometry.Topology.PiecewiseLinear
