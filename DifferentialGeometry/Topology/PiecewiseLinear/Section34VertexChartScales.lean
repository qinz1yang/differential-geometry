/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-! # Section34Vertex Chart Scales -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_chart_stability_scales_of_isCompact
    {X Y ι : Type*} [TopologicalSpace X] [MetricSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    {C : ι → Set X} {h : X → Y} {ε : ι → ℝ}
    (hC : ∀ i, IsCompact (C i)) (hh : ∀ i, ContinuousOn h (C i))
    (hε : ∀ i, 0 < ε i)
    (hchart : ∀ i, ∃ c ∈ (plGroupoid 3).maximalAtlas Y, h '' C i ⊆ c.source) :
    ∃ (c : ι → OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin 3))) (δ : ι → ℝ),
      (∀ i, c i ∈ (plGroupoid 3).maximalAtlas Y) ∧
      (∀ i, 0 < δ i) ∧ (∀ i, δ i < ε i) ∧
      ∀ G : ι → X → Y, (∀ i, ∀ x ∈ C i, dist (G i x) (h x) < δ i) →
        ∀ i, G i '' C i ⊆ (c i).source := by
  classical
  choose c hc hsource using hchart
  have hr (i : ι) : ∃ r : ℝ, 0 < r ∧
      Metric.cthickening r (h '' C i) ⊆ (c i).source :=
    ((hC i).image_of_continuousOn (hh i)).exists_cthickening_subset_open
      (c i).open_source (hsource i)
  choose r hr hcontain using hr
  let δ (i : ι) := min (ε i) (r i) / 2
  have hδ (i : ι) : 0 < δ i := half_pos (lt_min (hε i) (hr i))
  have hδε (i : ι) : δ i < ε i :=
    (half_lt_self (lt_min (hε i) (hr i))).trans_le (min_le_left _ _)
  have hδr (i : ι) : δ i < r i :=
    (half_lt_self (lt_min (hε i) (hr i))).trans_le (min_le_right _ _)
  refine ⟨c, δ, hc, hδ, hδε, fun G hG i => ?_⟩
  rintro y ⟨x, hx, rfl⟩
  apply hcontain i
  apply Metric.thickening_subset_cthickening
  exact Metric.mem_thickening_iff.mpr ⟨h x, ⟨x, hx, rfl⟩, (hG i x hx).trans (hδr i)⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_vertex_chart_stability_scales
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ (c : Section34VertexIndex 𝒦 𝒦' →
        OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
      (δ : Section34VertexIndex 𝒦 𝒦' → ℝ),
      (∀ w, c w ∈ (plGroupoid 3).maximalAtlas M₂) ∧
      (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
      ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
        ∀ w, G w '' Cc w ⊆ (c w).source := by
  obtain ⟨hε, hcc, hsubs, hchart, -⟩ := id hprep
  have hcont : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  exact exists_chart_stability_scales_of_isCompact (fun w => (hcc w).isCompact)
    (fun w => hcont.mono (hsubs w).2.2) hε hchart

end DifferentialGeometry.Topology.PiecewiseLinear
