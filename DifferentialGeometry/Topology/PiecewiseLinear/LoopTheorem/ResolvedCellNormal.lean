/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingSource

/-!
# The resolved cell of a cross seam resolution is again normal

`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube` carries the model
computation of the cross seam resolution into the manifold, but it *assumes* the normality of
the resolved cell: `CrossSeamRegluedData` has a field `normal : NormalSingularCellData cell
BdM B`. This file discharges that field from the remaining six fields of the structure together
with the corresponding properties of the reglued cell `G`, so that `normal` can be deleted from
`CrossSeamRegluedData` and replaced by `CrossSeamRegluedData.normalOfTube`.

## The shape of every proof

Every argument is the case split `G x ∈ U` or `G x ∉ U` of
`CrossSeamRegluedData.mem_tube_or_notMem_tube`. Inside the tube the resolved cell is the model
chord resolution read through the tube parametrisation, where it is injective
(`CrossSeamTubeData.injOn_resolved_tube`) and takes its values in the tube
(`CrossSeamTubeData.mapsTo_resolved_tube`); outside the tube it is `G`, and its values avoid the
tube. The two halves never interfere, because the first lands in the tube and the second does
not: that separation is what makes local injectivity, the fibre bound and the double point
inclusion transfer without any further geometric input.

## What is proved and what is assumed

Of the six fields of `NormalSingularCellData`, five are established here, and
`CrossSeamTubeData.normalOfResolvedCell` collects them together with the sixth:

* `singularSet` is `NormalSingularSetTriangulation.deletedBranchTriangulation` applied to the
  double point set of the resolved cell, which is `CrossSeamRegluedData.doublePointSet_cell_eq`;
  no `T2Space` assumption is needed for it, only the branch *bijection* of `BranchDeletion`
  needs one;
* `locallyInjective` and `fiber_le_two` need nothing but the same two properties of `G`;
* `crossing` needs the crossing property of `G` at the double points lying outside the tube,
  witnessed by a chart whose source misses the parametrised model cylinder. The extra clause is
  unavoidable here: `HasPLDoubleCrossingAt` constrains the whole source set `D.domain ∩ D ⁻¹'
  e.source`, and that set changes with the resolution exactly over the part of the chart lying
  in the tube. Once the chart source misses the cylinder the two source sets are equal and
  `HasPLNormalDoubleCrossingAt.congr_source` finishes;
* `boundary_image_subset` and `image_inter_boundary` need the two end cross sections
  `spliceEndDisks` of the tube: the resolution does move the boundary curve of the cell, inside
  the two end disks and nowhere else, so the statements that the end disks lie in the boundary
  surface `B` and that the tube meets `BdM` only in them are genuine extra inputs. They are
  taken as the named hypotheses `hendDisks`, `hends`, `htubeBdM` and `hBdM`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-! ### The boundary curve of a singular two cell -/

/-- The range of the boundary map of a singular two cell is the image of the frontier of its
source disk. -/
theorem SingularTwoCell.range_boundary_eq_image_frontier {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (D : SingularTwoCell M) :
    Set.range ⇑D.boundary = ⇑D '' frontier D.domain := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-! ### The two end cross sections of the model cylinder -/

/-- The two end cross sections of the model cylinder: the cross section squares lying over the
two endpoints of the base interval. For a boundary branch these are the two disks in which the
tube meets the boundary of the manifold, and they are the only place where the seam resolution
moves the boundary curve of the cell. -/
def spliceEndDisks : Set ((ℝ × ℝ) × ℝ) := spliceSquare ×ˢ ({0, 1} : Set ℝ)

/-- The two end cross sections lie in the model cylinder. -/
theorem spliceEndDisks_subset_spliceCylinder : spliceEndDisks ⊆ spliceCylinder := by
  rintro p ⟨hp, ht⟩
  refine ⟨hp, ?_⟩
  rcases ht with h | h
  · rw [h]
    exact ⟨le_refl (0 : ℝ), zero_le_one⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨zero_le_one, le_refl (1 : ℝ)⟩

/-- The fiberwise resolution does not move the base coordinate, on either source strip. -/
theorem crossSeamResolve_snd (q : Bool × ((ℝ × ℝ) × ℝ)) : (crossSeamResolve q).2 = q.2.2 := by
  obtain ⟨b, x⟩ := q
  cases b
  · exact crossSeamResolveNeg_snd x
  · exact crossSeamResolvePos_snd x

/-- A point of the model source lying over an end of the base interval is carried by the
resolution into the corresponding end cross section: the resolution acts on the cross section
only. -/
theorem crossSeamResolve_mem_spliceEndDisks {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource)
    (hend : q.2.2 = 0 ∨ q.2.2 = 1) : crossSeamResolve q ∈ spliceEndDisks := by
  have hfig : crossSeamResolve q ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨q, hq, rfl⟩
  refine ⟨(spliceFigure_subset_spliceCylinder hfig).1, ?_⟩
  rw [crossSeamResolve_snd]
  rcases hend with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

/-! ### The resolved cell over and away from the tube -/

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G cell : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

/-- Away from the tube the resolved cell takes its values outside the tube. This is the
unbundled form of `CrossSeamRegluedData.cell_notMem_tube`. -/
theorem notMem_tube_of_eqOn_compl (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' U))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain \ ⇑G ⁻¹' U) : ⇑cell x ∉ U := by
  rw [hcompl hx]
  exact hx.2

namespace CrossSeamTubeData

/-- Over the tube a resolved cell covers exactly the parametrised replacement figure. This is
the unbundled form of `CrossSeamRegluedData.image_cell_tube`, restated without that bundle so
that the derivation of normality does not go through the very field it removes. -/
theorem image_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U)) :
    ⇑cell '' (G.domain ∩ ⇑G ⁻¹' U) = T.chart '' spliceFigure := by
  have h : ⇑cell '' (G.domain ∩ ⇑G ⁻¹' U)
      = (T.chart ∘ crossSeamResolve ∘ coord) '' (G.domain ∩ ⇑G ⁻¹' U) :=
    Set.image_congr fun x hx => hresolved hx
  rw [h, Set.image_comp, Set.image_comp, hcoord.image_eq, image_crossSeamResolve]

/-- The resolution keeps the part of the source disk lying over the tube inside the tube. This
is the unbundled form of `CrossSeamRegluedData.mapsTo_cell_tube`. -/
theorem mapsTo_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U)) :
    MapsTo cell (G.domain ∩ ⇑G ⁻¹' U) U := by
  intro x hx
  have h : ⇑cell x ∈ ⇑cell '' (G.domain ∩ ⇑G ⁻¹' U) := ⟨x, hx, rfl⟩
  rw [T.image_resolved_tube hcoord hresolved] at h
  exact T.isTube.image_subset_tube (Set.image_mono spliceFigure_subset_spliceCylinder h)

/-- The resolution is injective over the tube: the two chord sheets are disjoint. This is the
unbundled form of `CrossSeamRegluedData.injOn_cell_tube`. -/
theorem injOn_resolved_tube (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U)) :
    InjOn cell (G.domain ∩ ⇑G ⁻¹' U) := by
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

/-- **Every double point of the resolved cell is a double point of the reglued cell lying
outside the tube.** Inside the tube the resolution is injective, and a value taken inside the
tube is never taken again outside it, so no double point survives in the tube and no new one is
created. This is the local form of `CrossSeamRegluedData.doublePointSet_cell_eq` that the
crossing condition consumes; unlike that statement it needs no hypothesis on `G`. -/
theorem doublePointSet_resolved_subset (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource)
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' U)) :
    doublePointSet cell cell.domain ⊆ doublePointSet G G.domain \ U := by
  rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
  rw [hdomain] at hx hz
  by_cases hxU : ⇑G x ∈ U
  · by_cases hzU : ⇑G z ∈ U
    · exact absurd (T.injOn_resolved_tube hcoord hresolved ⟨hx, hxU⟩ ⟨hz, hzU⟩
        (hyx.trans hyz.symm)) hxz
    · have h1 : y ∈ U := by
        rw [← hyx]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨hx, hxU⟩
      have h2 : y ∉ U := by
        rw [← hyz]
        exact notMem_tube_of_eqOn_compl hcompl ⟨hz, hzU⟩
      exact absurd h1 h2
  · by_cases hzU : ⇑G z ∈ U
    · have h1 : y ∈ U := by
        rw [← hyz]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨hz, hzU⟩
      have h2 : y ∉ U := by
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

/-! ### The resolved cell is a normal singular cell -/

/-- **The resolved cell of a cross seam resolution is again a normal singular cell.** The data
`hdomain`, `hcoord`, `hreglued`, `hresolved` and `hcompl` are exactly the geometric fields of
`CrossSeamRegluedData` other than `normal`, and `hdouble` is its conclusion
`CrossSeamRegluedData.doublePointSet_cell_eq`; the remaining hypotheses are the properties of
the reglued cell `G` and of the tube that the resolution uses.

Their content is:

* `hGinj`, `hGfiber`, `hGboundary`, `hGimage` : the four elementary fields of a normal singular
  cell for the reglued cell `G`, which is not itself asserted to be normal;
* `hGcrossing` : at each of its double points lying outside the tube, `G` has a normal double
  crossing in a chart whose source misses the parametrised model cylinder. The last clause is
  what makes the source set of the crossing condition unchanged by the resolution;
* `hendDisks` : the two end cross sections of the tube lie in the boundary surface `B`;
* `hends` : over the tube, a point of the source disk lies on the boundary of the source disk
  exactly when it lies over one of the two ends of the base interval, that is, the two source
  strips run from one end of the tube to the other;
* `htubeBdM` : the tube meets the boundary of the manifold only in its two end cross sections;
* `hBdM` : the surface `B` in which the boundary curve of the cell runs lies in the boundary
  `BdM` of the manifold. -/
noncomputable def normalOfResolvedCell (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord) (G.domain ∩ ⇑G ⁻¹' U))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' U))
    (hdouble : doublePointSet cell cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c)
    (hGinj : ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn G V)
    (hGfiber : ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2)
    (hGboundary : Set.range ⇑G.boundary ⊆ B)
    (hGimage : ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary)
    (hGcrossing : ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        Disjoint e.source (T.chart '' spliceCylinder) ∧
          HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' U,
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : U ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM) :
    NormalSingularCellData cell BdM B where
  locallyInjective := by
    intro x hx
    rw [hdomain] at hx ⊢
    obtain ⟨V, hV, hinj⟩ := hGinj x hx
    refine ⟨V ∩ G.domain, Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro x₁ h₁ x₂ h₂ heq
    by_cases h₁U : ⇑G x₁ ∈ U
    · by_cases h₂U : ⇑G x₂ ∈ U
      · exact T.injOn_resolved_tube hcoord hresolved ⟨h₁.2, h₁U⟩ ⟨h₂.2, h₂U⟩ heq
      · exact absurd (heq ▸ T.mapsTo_resolved_tube hcoord hresolved ⟨h₁.2, h₁U⟩)
          (notMem_tube_of_eqOn_compl hcompl ⟨h₂.2, h₂U⟩)
    · by_cases h₂U : ⇑G x₂ ∈ U
      · exact absurd (heq ▸ notMem_tube_of_eqOn_compl hcompl ⟨h₁.2, h₁U⟩)
          (fun hmem => hmem (T.mapsTo_resolved_tube hcoord hresolved ⟨h₂.2, h₂U⟩))
      · refine hinj h₁.1 h₂.1 ?_
        rw [← hcompl ⟨h₁.2, h₁U⟩, ← hcompl ⟨h₂.2, h₂U⟩]
        exact heq
  fiber_le_two := by
    intro y
    rw [hdomain]
    by_cases hyU : y ∈ U
    · refine le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro a b ha hb
      have hatube : a ∈ G.domain ∩ ⇑G ⁻¹' U := by
        refine ⟨ha.1, ?_⟩
        by_contra hnot
        exact notMem_tube_of_eqOn_compl hcompl ⟨ha.1, hnot⟩ (ha.2 ▸ hyU)
      have hbtube : b ∈ G.domain ∩ ⇑G ⁻¹' U := by
        refine ⟨hb.1, ?_⟩
        by_contra hnot
        exact notMem_tube_of_eqOn_compl hcompl ⟨hb.1, hnot⟩ (hb.2 ▸ hyU)
      exact T.injOn_resolved_tube hcoord hresolved hatube hbtube (ha.2.trans hb.2.symm)
    · refine le_trans (Set.encard_le_encard ?_) (hGfiber y)
      rintro a ⟨ha, hay⟩
      have hacompl : a ∈ G.domain \ ⇑G ⁻¹' U := by
        refine ⟨ha, fun hmem => hyU ?_⟩
        rw [← hay]
        exact T.mapsTo_resolved_tube hcoord hresolved ⟨ha, hmem⟩
      exact ⟨ha, by rw [mem_preimage, ← hcompl hacompl]; exact hay⟩
  boundary_image_subset := by
    rw [SingularTwoCell.range_boundary_eq_image_frontier, hdomain]
    rintro _ ⟨x, hx, rfl⟩
    have hxdom : x ∈ G.domain := G.frontier_subset_domain hx
    by_cases hxU : ⇑G x ∈ U
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
      by_cases hxU : ⇑G x ∈ U
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
        have hx'U : ⇑G x' ∉ U := by
          rw [hGx']
          exact hxU
        exact ⟨x', hx', by rw [hcompl ⟨hx'dom, hx'U⟩, hcompl ⟨hx, hxU⟩]; exact hGx'⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxdom : x ∈ G.domain := G.frontier_subset_domain hx
      refine ⟨⟨x, hxdom, rfl⟩, ?_⟩
      by_cases hxU : ⇑G x ∈ U
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
    obtain ⟨hyG, hyU⟩ :=
      T.doublePointSet_resolved_subset hdomain hcoord hresolved hcompl hy
    obtain ⟨e, he, hye, hdis, hcross⟩ := hGcrossing y hyG hyU
    have hnot : ∀ x ∈ G.domain, ⇑G x ∈ e.source ∨ ⇑cell x ∈ e.source → ⇑G x ∉ U := by
      rintro x hx (hsrc | hsrc) hmem
      · refine Set.disjoint_left.mp hdis hsrc ⟨crossSeamInclude (coord x), ?_, ?_⟩
        · refine bentFigure_subset_spliceCylinder ?_
          rw [← image_crossSeamInclude]
          exact ⟨coord x, hcoord.mapsTo ⟨hx, hmem⟩, rfl⟩
        · exact (hreglued ⟨hx, hmem⟩).symm
      · refine Set.disjoint_left.mp hdis hsrc ?_
        have himg : ⇑cell x ∈ T.chart '' spliceFigure := by
          rw [← T.image_resolved_tube hcoord hresolved]
          exact ⟨x, ⟨hx, hmem⟩, rfl⟩
        exact Set.image_mono spliceFigure_subset_spliceCylinder himg
    have hset : cell.domain ∩ ⇑cell ⁻¹' e.source = G.domain ∩ ⇑G ⁻¹' e.source := by
      rw [hdomain]
      apply Subset.antisymm
      · rintro x ⟨hx, hsrc⟩
        exact ⟨hx, by rw [mem_preimage, ← hcompl ⟨hx, hnot x hx (Or.inr hsrc)⟩]; exact hsrc⟩
      · rintro x ⟨hx, hsrc⟩
        exact ⟨hx, by rw [mem_preimage, hcompl ⟨hx, hnot x hx (Or.inl hsrc)⟩]; exact hsrc⟩
    refine ⟨e, he, hye, ?_⟩
    rw [hset]
    refine hcross.congr_source ?_
    rintro x ⟨hx, hsrc⟩
    exact congrArg e (hcompl ⟨hx, hnot x hx (Or.inl hsrc)⟩).symm

end CrossSeamTubeData

/-! ### The assumed field of the reglued data is derivable -/

namespace CrossSeamRegluedData

variable {T : CrossSeamTubeData hD c U}

/-- **The `normal` field of `CrossSeamRegluedData` is derivable from its other fields.** The
proof passes only the six geometric fields of `R` to
`CrossSeamTubeData.normalOfResolvedCell`, so the field `normal` of `CrossSeamRegluedData` may
be deleted and every use of `R.normal` replaced by `R.normalOfTube` applied to the same extra
hypotheses. The hypothesis `hGD`, which says that the cross reglue changes no double point
outside the tube, is the one already consumed by
`CrossSeamRegluedData.doublePointSet_cell_eq`; the remaining hypotheses are described at
`CrossSeamTubeData.normalOfResolvedCell`. -/
noncomputable def normalOfTube (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ U = doublePointSet D D.domain \ U)
    (hGinj : ∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn G V)
    (hGfiber : ∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2)
    (hGboundary : Set.range ⇑G.boundary ⊆ B)
    (hGimage : ⇑G '' G.domain ∩ BdM = Set.range ⇑G.boundary)
    (hGcrossing : ∀ y ∈ doublePointSet G G.domain, y ∉ U →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        Disjoint e.source (T.chart '' spliceCylinder) ∧
          HasPLNormalDoubleCrossingAt (e ∘ G) (G.domain ∩ ⇑G ⁻¹' e.source)
            (e '' (e.source ∩ BdM)) (e y))
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' U,
      x ∈ frontier G.domain ↔ (R.coord x).2.2 = 0 ∨ (R.coord x).2.2 = 1)
    (htubeBdM : U ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM) :
    NormalSingularCellData R.cell BdM B :=
  T.normalOfResolvedCell R.domain_eq R.bijOn_coord R.reglued_eq R.resolved_eq R.eqOn_compl
    (R.doublePointSet_cell_eq hGD) hGinj hGfiber hGboundary hGimage hGcrossing hendDisks
    hends htubeBdM hBdM

end CrossSeamRegluedData

end DifferentialGeometry.Topology.PiecewiseLinear
