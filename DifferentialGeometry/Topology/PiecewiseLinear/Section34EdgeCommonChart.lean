/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldCofaces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConnectedCarriers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

open Classical in
theorem exists_section34Edge_triangle
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ s : Section34SimplexIndex 𝒦 3, Section34Incident e.1 s.1 := by
  classical
  have hman := hframe.1
  have hsub := hframe.2.1
  have hmap := hframe.2.2.1
  let x : Ea := e.1.centroid ℝ id
  have hxopen : x ∈ openSimplex e.1 :=
    centroid_mem_openSimplex (𝒦'.complex.nonempty_of_mem_faces e.2.1)
  have hxHull : x ∈ convexHull ℝ (e.1 : Set Ea) :=
    openSimplex_subset_convexHull e.1 hxopen
  have hxK' : x ∈ 𝒦'.complex.space := 𝒦'.complex.convexHull_subset_space e.2.1 hxHull
  have hxK : x ∈ 𝒦.complex.space := hsub.1 ▸ hxK'
  have hxGraph : 𝒦.map x ∈ graphSkeletonSpace 𝒦 := by
    rw [← hmap]
    exact e.2.2.2 ⟨x, hxHull, rfl⟩
  change 𝒦.map x ∈ ⋃ q ∈ {q : Finset Ea | q ∈ 𝒦.complex.faces ∧ q.card ≤ 2},
    simplexBody 𝒦 q at hxGraph
  obtain ⟨q, ⟨hq, hqcard⟩, y, hy, hyx⟩ := mem_iUnion₂.mp hxGraph
  have hyx' : y = x :=
    𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space hq hy) hxK hyx
  subst y
  have heq : convexHull ℝ (e.1 : Set Ea) ⊆ convexHull ℝ (q : Set Ea) :=
    hsub.convexHull_subset_of_mem_openSimplex hq e.2.1 hxopen hy
  obtain ⟨t, ht, hqt, htcard⟩ := 𝒦.exists_tetrahedron_superset hman hq
  obtain ⟨s, hqs, hst, hscard⟩ :=
    Finset.exists_subsuperset_card_eq hqt (by omega) (by omega : 3 ≤ t.card)
  have hs : s ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed ht hst (Finset.Nonempty.mono hqs (𝒦.complex.nonempty_of_mem_faces hq))
  refine ⟨⟨s, hs, hscard⟩, ?_⟩
  exact (subset_convexHull ℝ (e.1 : Set Ea)).trans
    (heq.trans (convexHull_mono (Finset.coe_subset.mpr hqs)))

open Classical in
theorem exists_section34Edge_common_chart
    {h : M₁ → M₂} {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {ct : Section34SimplexIndex 𝒦 3 →
      OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
    {ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ s : Section34SimplexIndex 𝒦 3,
      Section34Incident e.1 s.1 ∧
      Section34Incident (ends e).1.1 s.1 ∧
      Section34Incident (ends e).2.1 s.1 ∧
      ct s ∈ (plGroupoid 3).maximalAtlas M₂ ∧
      Q (ends e).1 ∪ Q (ends e).2 ⊆ (ct s).source := by
  obtain ⟨s, hse⟩ := exists_section34Edge_triangle hframe e
  have hs₁ : Section34Incident (ends e).1.1 s.1 := by
    change ((ends e).1.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    have hsub : ((ends e).1.1 : Set Ea) ⊆ (e.1 : Set Ea) := by
      rw [hends e]
      exact subset_union_left
    exact hsub.trans hse
  have hs₂ : Section34Incident (ends e).2.1 s.1 := by
    change ((ends e).2.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    have hsub : ((ends e).2.1 : Set Ea) ⊆ (e.1 : Set Ea) := by
      rw [hends e]
      exact subset_union_right
    exact hsub.trans hse
  obtain ⟨hct, hsource⟩ := htor.1 s
  refine ⟨s, hse, hs₁, hs₂, hct, ?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact hsource (mem_iUnion₂.mpr ⟨(ends e).1, hs₁, hy⟩)
  · exact hsource (mem_iUnion₂.mpr ⟨(ends e).2, hs₂, hy⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
