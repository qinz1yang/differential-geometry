/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldCofaces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {f₁ : M₁ → M₂} {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem Section34CutFrame.exists_tetrahedron_of_subdivision_face
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {s : Finset Ea}
    (hs : s ∈ 𝒦'.complex.faces) :
    ∃ t : Section34SimplexIndex 𝒦 4, Section34Incident s t.1 := by
  obtain ⟨r, hr, hsr⟩ := hcut.2.1.exists_face_subset hs
  obtain ⟨t, ht, hrt, hcard⟩ := 𝒦.exists_tetrahedron_superset hcut.1 hr
  refine ⟨⟨t, ht, hcard⟩, ?_⟩
  exact (subset_convexHull ℝ _).trans
    (hsr.trans (convexHull_mono (Finset.coe_subset.mpr hrt)))

theorem Section34CutFrame.exists_simplexIndex_four_of_edge
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ t : Section34SimplexIndex 𝒦 4, Section34Incident e.1 t.1 := by
  exact hcut.exists_tetrahedron_of_subdivision_face e.2.1

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.exists_chart_tetrahedron
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (t : Section34SimplexIndex 𝒦 4) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, H t.1 ⊆ c.source ∧
      (∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t.1 → tgtV w ⊆ c.source) ∧
      ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 → fbl s ⊆ c.source := by
  obtain ⟨-, hcarrier, -, hext, -⟩ := hdata
  obtain ⟨-, -, -, -, -, hchart⟩ := hcarrier
  obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
  have hobs := (hext.1 t).trans (interior_subset.trans hHc)
  refine ⟨c, hc, hHc, ?_, ?_⟩
  · intro w hw z hz
    exact hobs (Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hw⟩, rfl, hz⟩))
  · intro s hs z hz
    exact hobs (Or.inr (mem_iUnion₂.mpr ⟨s, hs, hz⟩))

theorem Section34NormalPlus.exists_chart_vertexBalls_of_edge
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 → tgtV w ⊆ c.source := by
  obtain ⟨t, het⟩ := hdata.1.exists_simplexIndex_four_of_edge e
  obtain ⟨c, hc, -, hVc, -⟩ := hdata.exists_chart_tetrahedron t
  exact ⟨c, hc, fun w hw => hVc w ((Finset.coe_subset.mpr hw).trans het)⟩

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.vertexBall_boundary_eq_image
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (w : Section34VertexIndex 𝒦 𝒦') :
    tgtVBd w = section34VertexBallImage srcBd f₁ w := by
  obtain ⟨hcut, -, hgraph, -, -, hV, -, hcell, -⟩ := hdata
  have himage := hcut.isPLCellOn_vertexBallImage hgraph.2.2.1 w
  have htarget := hcell w
  rw [hV w] at htarget
  exact htarget.boundary_eq himage

omit [FiniteDimensional ℝ Ea] in
theorem Section34NormalPlus.splitDisk_boundary_eq_image
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) (e : Section34EdgeIndex 𝒦 𝒦') :
    tgtEBd e = section34SplitDiskImage srcBd f₁ e := by
  obtain ⟨hcut, -, hgraph, -, -, -, hE, -, hcell, -⟩ := hdata
  have himage := hcut.isPLCellOn_splitDiskImage hgraph.2.2.1 e
  have htarget := hcell e
  rw [hE e] at htarget
  exact htarget.boundary_eq himage

end DifferentialGeometry.Topology.PiecewiseLinear
