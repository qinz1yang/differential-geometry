/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingLocality
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem SingularTwoCell.range_boundary_eq_image_frontier {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (D : SingularTwoCell M) :
    Set.range ⇑D.boundary = ⇑D '' frontier D.domain := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G cell : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

theorem notMem_tube_of_eqOn_compl (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' U))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain \ ⇑G ⁻¹' U) : ⇑cell x ∉ U := by
  rw [hcompl hx]
  exact hx.2

namespace CrossSeamTubeData

theorem image_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))) :
    ⇑cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = T.chart '' spliceFigure := by
  have h : ⇑cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = (T.chart ∘ crossSeamResolve ∘ coord) ''
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    Set.image_congr fun x hx => hresolved hx
  rw [h, Set.image_comp, Set.image_comp, hcoord.image_eq, image_crossSeamResolve]

theorem mapsTo_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))) :
    MapsTo cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      (T.chart '' spliceCylinder) := by
  intro x hx
  have h : ⇑cell x ∈ ⇑cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := ⟨x, hx, rfl⟩
  rw [T.image_resolved_tube hcoord hresolved] at h
  exact Set.image_mono spliceFigure_subset_spliceCylinder h

theorem injOn_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))) :
    InjOn cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
  intro x hx z hz hxz
  have hxm : coord x ∈ bentSource := hcoord.mapsTo hx
  have hzm : coord z ∈ bentSource := hcoord.mapsTo hz
  have hxs : crossSeamResolve (coord x) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hxm, rfl⟩
  have hzs : crossSeamResolve (coord z) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hzm, rfl⟩
  rw [hresolved hx, hresolved hz] at hxz
  simp only [Function.comp_apply] at hxz
  have hmodel : crossSeamResolve (coord x) = crossSeamResolve (coord z) :=
    T.isTube.injOn_chart (spliceFigure_subset_spliceCylinder hxs)
      (spliceFigure_subset_spliceCylinder hzs) hxz
  exact hcoord.injOn hx hz (injOn_crossSeamResolve hxm hzm hmodel)

theorem doublePointSet_resolved_subset (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder))) :
    doublePointSet cell cell.domain ⊆
      doublePointSet G G.domain \ T.chart '' spliceCylinder := by
  rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
  rw [hdomain] at hx hz
  by_cases hxU : ⇑G x ∈ T.chart '' spliceCylinder
  · by_cases hzU : ⇑G z ∈ T.chart '' spliceCylinder
    · exact absurd (T.injOn_resolved_tube hcoord hresolved ⟨hx, hxU⟩ ⟨hz, hzU⟩
        (hyx.trans hyz.symm)) hxz
    · have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyx]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨hx, hxU⟩
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyz]
        exact notMem_tube_of_eqOn_compl hcompl ⟨hz, hzU⟩
      exact absurd h1 h2
  · by_cases hzU : ⇑G z ∈ T.chart '' spliceCylinder
    · have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyz]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨hz, hzU⟩
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyx]
        exact notMem_tube_of_eqOn_compl hcompl ⟨hx, hxU⟩
      exact absurd h1 h2
    · refine ⟨⟨x, hx, z, hz, hxz, ?_, ?_⟩, ?_⟩
      · rw [← hcompl ⟨hx, hxU⟩]
        exact hyx
      · rw [← hcompl ⟨hz, hzU⟩]
        exact hyz
      · rw [← hyx]
        exact notMem_tube_of_eqOn_compl hcompl ⟨hx, hxU⟩

noncomputable def normalOfResolvedCell [T2Space M] (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c)
    (hGinj : ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn G V)
    (hGfiber : ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2)
    (hGboundary : Set.range ⇑G.boundary ⊆ B)
    (hGimage : ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary)
    (hGcrossing : ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM) :
    NormalSingularCellData cell BdM B where
  locallyInjective := by
    intro x hx
    rw [hdomain] at hx ⊢
    obtain ⟨V, hV, hinj⟩ := hGinj x hx
    refine ⟨V ∩ G.domain, Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro x₁ h₁ x₂ h₂ heq
    by_cases h₁U : ⇑G x₁ ∈ T.chart '' spliceCylinder
    · by_cases h₂U : ⇑G x₂ ∈ T.chart '' spliceCylinder
      · exact T.injOn_resolved_tube hcoord hresolved ⟨h₁.2, h₁U⟩ ⟨h₂.2, h₂U⟩ heq
      · exact absurd (heq ▸ T.mapsTo_resolved_tube hcoord hresolved ⟨h₁.2, h₁U⟩)
          (notMem_tube_of_eqOn_compl hcompl ⟨h₂.2, h₂U⟩)
    · by_cases h₂U : ⇑G x₂ ∈ T.chart '' spliceCylinder
      · exact absurd (heq ▸ notMem_tube_of_eqOn_compl hcompl ⟨h₁.2, h₁U⟩)
          (fun hmem => hmem (T.mapsTo_resolved_tube hcoord hresolved ⟨h₂.2, h₂U⟩))
      · refine hinj h₁.1 h₂.1 ?_
        rw [← hcompl ⟨h₁.2, h₁U⟩, ← hcompl ⟨h₂.2, h₂U⟩]
        exact heq
  fiber_le_two := by
    intro y
    rw [hdomain]
    by_cases hyU : y ∈ T.chart '' spliceCylinder
    · refine le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro a b ha hb
      have hatube : a ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder) := by
        refine ⟨ha.1, ?_⟩
        by_contra hnot
        exact notMem_tube_of_eqOn_compl hcompl ⟨ha.1, hnot⟩ (ha.2 ▸ hyU)
      have hbtube : b ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder) := by
        refine ⟨hb.1, ?_⟩
        by_contra hnot
        exact notMem_tube_of_eqOn_compl hcompl ⟨hb.1, hnot⟩ (hb.2 ▸ hyU)
      exact T.injOn_resolved_tube hcoord hresolved hatube hbtube (ha.2.trans hb.2.symm)
    · refine le_trans (Set.encard_le_encard ?_) (hGfiber y)
      rintro a ⟨ha, hay⟩
      have hacompl : a ∈ G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder) := by
        refine ⟨ha, fun hmem => hyU ?_⟩
        rw [← hay]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨ha, hmem⟩
      exact ⟨ha, by rw [mem_preimage, ← hcompl hacompl]; exact hay⟩
  boundary_image_subset := by
    rw [SingularTwoCell.range_boundary_eq_image_frontier, hdomain]
    rintro _ ⟨x, hx, rfl⟩
    have hxdom : x ∈ G.domain := G.frontier_subset_domain hx
    by_cases hxU : ⇑G x ∈ T.chart '' spliceCylinder
    · rw [hresolved ⟨hxdom, hxU⟩]
      exact hendDisks ⟨crossSeamResolve (coord x),
        crossSeamResolve_mem_spliceEndDisks (hcoord.mapsTo ⟨hxdom, hxU⟩)
          ((hends x ⟨hxdom, hxU⟩).mp hx), rfl⟩
    · rw [hcompl ⟨hxdom, hxU⟩]
      exact hGboundary ⟨⟨x, hx⟩, rfl⟩
  image_inter_boundary := by
    rw [SingularTwoCell.range_boundary_eq_image_frontier, hdomain]
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hbd⟩
      by_cases hxU : ⇑G x ∈ T.chart '' spliceCylinder
      · refine ⟨x, (hends x ⟨hx, hxU⟩).mpr ?_, rfl⟩
        obtain ⟨p, hp, hpx⟩ :=
          htubeBdM ⟨T.mapsTo_resolved_tube hcoord hresolved ⟨hx, hxU⟩, hbd⟩
        have hres : T.chart (crossSeamResolve (coord x)) = T.chart p := by
          rw [hpx, hresolved ⟨hx, hxU⟩]
          rfl
        have hfig : crossSeamResolve (coord x) ∈ spliceFigure := by
          rw [← image_crossSeamResolve]
          exact ⟨coord x, hcoord.mapsTo ⟨hx, hxU⟩, rfl⟩
        have heq : crossSeamResolve (coord x) = p :=
          T.isTube.injOn_chart (spliceFigure_subset_spliceCylinder hfig)
            (spliceEndDisks_subset_spliceCylinder hp) hres
        have hsnd : (coord x).2.2 = p.2 := by rw [← crossSeamResolve_snd, heq]
        rcases hp.2 with h | h
        · exact Or.inl (hsnd.trans h)
        · exact Or.inr (hsnd.trans (Set.mem_singleton_iff.mp h))
      · have hmem : ⇑G x ∈ ⇑G '' G.domain ∩ BdM :=
          ⟨⟨x, hx, rfl⟩, by rw [← hcompl ⟨hx, hxU⟩]; exact hbd⟩
        rw [hGimage, SingularTwoCell.range_boundary_eq_image_frontier] at hmem
        obtain ⟨x', hx', hGx'⟩ := hmem
        have hx'dom : x' ∈ G.domain := G.frontier_subset_domain hx'
        have hx'U : ⇑G x' ∉ T.chart '' spliceCylinder := by
          rw [hGx']
          exact hxU
        exact ⟨x', hx', by rw [hcompl ⟨hx'dom, hx'U⟩, hcompl ⟨hx, hxU⟩]; exact hGx'⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxdom : x ∈ G.domain := G.frontier_subset_domain hx
      refine ⟨⟨x, hxdom, rfl⟩, ?_⟩
      by_cases hxU : ⇑G x ∈ T.chart '' spliceCylinder
      · rw [hresolved ⟨hxdom, hxU⟩]
        refine hBdM (hendDisks ⟨crossSeamResolve (coord x), ?_, rfl⟩)
        exact crossSeamResolve_mem_spliceEndDisks (hcoord.mapsTo ⟨hxdom, hxU⟩)
          ((hends x ⟨hxdom, hxU⟩).mp hx)
      · have hmem : ⇑G x ∈ Set.range ⇑G.boundary := ⟨⟨x, hx⟩, rfl⟩
        rw [← hGimage] at hmem
        rw [hcompl ⟨hxdom, hxU⟩]
        exact hmem.2
  singularSet := hD.singularSet.deletedBranchTriangulation c hdouble
  crossing := by
    intro y hy
    have hyU : y ∉ U := by
      have hyD := hy
      rw [hdouble, T.doublePointSet_sdiff_branchCarrier] at hyD
      exact hyD.2
    have hyG : y ∈ doublePointSet G G.domain :=
      (T.doublePointSet_resolved_subset hdomain hcoord hresolved hcompl hy).1
    obtain ⟨e, he, hye, hcross⟩ := hGcrossing y hyG hyU
    have hoff : ∀ z ∈ e.source, ⇑e z ∈ ⇑e '' (e.source \ T.chart '' spliceCylinder) →
        z ∉ T.chart '' spliceCylinder := by
      rintro z hz ⟨w, hw, hwz⟩ hmem
      exact hw.2 (by rw [e.injOn hw.1 hz hwz]; exact hmem)
    have hcelloff : ∀ x ∈ G.domain, ⇑cell x ∈ e.source →
        ⇑e (⇑cell x) ∈ ⇑e '' (e.source \ T.chart '' spliceCylinder) →
        ⇑G x ∉ T.chart '' spliceCylinder := by
      intro x hx hsrc hxV hmem
      exact hoff (⇑cell x) hsrc hxV (T.mapsTo_resolved_tube hcoord hresolved ⟨hx, hmem⟩)
    have hVopen : IsOpen (⇑e '' (e.source \ T.chart '' spliceCylinder)) :=
      e.isOpen_image_of_subset_source
        (e.open_source.sdiff T.isCompact_image_spliceCylinder.isClosed) sdiff_subset
    have hyV : ⇑e y ∈ ⇑e '' (e.source \ T.chart '' spliceCylinder) :=
      ⟨y, ⟨hye, fun hmem => hyU (T.isTube.image_subset_tube hmem)⟩, rfl⟩
    have hg : ContinuousOn (⇑e ∘ ⇑cell) (cell.domain ∩ ⇑cell ⁻¹' e.source) :=
      e.continuousOn.comp (cell.continuousOn.mono inter_subset_left) fun _ hx => hx.2
    refine ⟨e, he, hye, hcross.of_eqOn_of_isOpen hg hVopen hyV ?_ ?_⟩
    · ext x
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply, hdomain]
      constructor
      · rintro ⟨⟨hx, hsrc⟩, hxV⟩
        rw [hcompl ⟨hx, hoff (⇑G x) hsrc hxV⟩]
        exact ⟨⟨hx, hsrc⟩, hxV⟩
      · rintro ⟨⟨hx, hsrc⟩, hxV⟩
        have hxc : ⇑cell x = ⇑G x := hcompl ⟨hx, hcelloff x hx hsrc hxV⟩
        rw [hxc] at hsrc hxV
        exact ⟨⟨hx, hsrc⟩, hxV⟩
    · rintro x ⟨⟨hx, hsrc⟩, hxV⟩
      exact congrArg (⇑e) (hcompl ⟨hx, hoff (⇑G x) hsrc hxV⟩).symm

end CrossSeamTubeData

namespace CrossSeamRegluedData

variable {T : CrossSeamTubeData hD c U}

noncomputable def normalOfTube [T2Space M] (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (hGinj : ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn G V)
    (hGfiber : ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2)
    (hGboundary : Set.range ⇑G.boundary ⊆ B)
    (hGimage : ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary)
    (hGcrossing : ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (R.coord x).2.2 = 0 ∨ (R.coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM) :
    NormalSingularCellData R.cell BdM B :=
  T.normalOfResolvedCell R.domain_eq R.bijOn_coord R.resolved_eq R.eqOn_compl
    (R.doublePointSet_cell_eq hGD) hGinj hGfiber hGboundary hGimage hGcrossing hendDisks
    hends htubeBdM hBdM

end CrossSeamRegluedData

end DifferentialGeometry.Topology.PiecewiseLinear
