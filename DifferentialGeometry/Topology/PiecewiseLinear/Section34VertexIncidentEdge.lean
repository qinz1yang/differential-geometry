/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeCommonChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M₁ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

open Classical in
theorem exists_section34Vertex_triangle
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (w : Section34VertexIndex 𝒦 𝒦') :
    ∃ s : Section34SimplexIndex 𝒦 3, Section34Incident w.1 s.1 := by
  classical
  have hman := hframe.1
  have hsub := hframe.2.1
  have hmap := hframe.2.2.1
  let x : Ea := w.1.centroid ℝ id
  have hxopen : x ∈ openSimplex w.1 :=
    centroid_mem_openSimplex (𝒦'.complex.nonempty_of_mem_faces w.2.1)
  have hxHull : x ∈ convexHull ℝ (w.1 : Set Ea) :=
    openSimplex_subset_convexHull w.1 hxopen
  have hxK' : x ∈ 𝒦'.complex.space := 𝒦'.complex.convexHull_subset_space w.2.1 hxHull
  have hxK : x ∈ 𝒦.complex.space := hsub.1 ▸ hxK'
  have hxGraph : 𝒦.map x ∈ graphSkeletonSpace 𝒦 := by
    rw [← hmap]
    exact w.2.2.2 ⟨x, hxHull, rfl⟩
  change 𝒦.map x ∈ ⋃ q ∈ {q : Finset Ea | q ∈ 𝒦.complex.faces ∧ q.card ≤ 2},
    simplexBody 𝒦 q at hxGraph
  obtain ⟨q, ⟨hq, hqcard⟩, y, hy, hyx⟩ := mem_iUnion₂.mp hxGraph
  have hyx' : y = x :=
    𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space hq hy) hxK hyx
  subst y
  have heq : convexHull ℝ (w.1 : Set Ea) ⊆ convexHull ℝ (q : Set Ea) :=
    hsub.convexHull_subset_of_mem_openSimplex hq w.2.1 hxopen hy
  obtain ⟨t, ht, hqt, htcard⟩ := 𝒦.exists_tetrahedron_superset hman hq
  obtain ⟨s, hqs, hst, hscard⟩ :=
    Finset.exists_subsuperset_card_eq hqt (by omega) (by omega : 3 ≤ t.card)
  have hs : s ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed ht hst (Finset.Nonempty.mono hqs (𝒦.complex.nonempty_of_mem_faces hq))
  refine ⟨⟨s, hs, hscard⟩, ?_⟩
  exact (subset_convexHull ℝ (w.1 : Set Ea)).trans
    (heq.trans (convexHull_mono (Finset.coe_subset.mpr hqs)))

open Classical in
theorem exists_section34Vertex_incident_edge
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (w : Section34VertexIndex 𝒦 𝒦') :
    ∃ e : Section34EdgeIndex 𝒦 𝒦',
      w = (ends e).1 ∨ w = (ends e).2 := by
  obtain ⟨s, hs⟩ := exists_section34Vertex_triangle hframe w
  obtain ⟨e, -, -, -, -, hwe, -, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hframe.2.1 hframe.2.2.1 s w hs
  exact ⟨e, eq_or_eq_of_section34VertexIndex_subset e (hends e) hwe⟩

end DifferentialGeometry.Topology.PiecewiseLinear
