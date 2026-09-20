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
computation of the cross seam resolution into the manifold. It does *not* assume the normality
of the resolved cell: `CrossSeamRegluedData` carries only the six geometric fields, and this
file derives the normality from them together with the corresponding properties of the reglued
cell `G`. `CrossSeamRegluedData.normalOfTube` is the resulting producer, and the consumers of
`CrossSeamTube` take its output as the explicit hypothesis `hnormal`.

## The shape of every proof

Every argument is the case split `G x ∈ T.chart '' spliceCylinder` or
`G x ∉ T.chart '' spliceCylinder` of `CrossSeamRegluedData.mem_tube_or_notMem_tube`, taken at
the closed parametrised cylinder and not at the open tube `U`. Over the cylinder the resolved
cell is the model chord resolution read through the tube parametrisation, where it is injective
(`CrossSeamTubeData.injOn_resolved_tube`) and takes its values in the cylinder
(`CrossSeamTubeData.mapsTo_resolved_tube`); off the cylinder it is `G`, and its values avoid the
cylinder. The two halves never interfere, because the first lands in the cylinder and the second
does not: that separation is what makes local injectivity, the fibre bound and the double point
inclusion transfer without any further geometric input.

The split set is `T.chart '' spliceCylinder` because that is how the fields of
`CrossSeamRegluedData` are stated: splitting along the open `U` would equate a compact image
with a relatively open piece of the connected image of the source disk, and so force the whole
reglued cell into the tube. The declarations below keep the word `tube` in their names, but the
set they split along is the closed parametrised cylinder throughout;
`CrossSeamTubeCore.image_subset_tube` is what carries a conclusion back to `U`.

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
  unavoidable here: `HasPLDoubleCrossingAt` constrains the whole source set
  `D.domain ∩ D ⁻¹' e.source`, and that set changes with the resolution exactly over the part
  of the chart lying in the cylinder. Once the chart source misses the cylinder the two source
  sets are equal and `HasPLNormalDoubleCrossingAt.congr_source` finishes. The double points of
  the resolved cell come out off the cylinder, and the field `hdouble` places them off the whole
  tube, so the hypothesis is still stated at the tube;
* `boundary_image_subset` and `image_inter_boundary` need the two end cross sections
  `spliceEndDisks` of the tube: the resolution does move the boundary curve of the cell, inside
  the two end disks and nowhere else, so the statements that the end disks lie in the boundary
  surface `B` and that the parametrised cylinder meets `BdM` only in them are genuine extra
  inputs. They are taken as the named hypotheses `hendDisks`, `hends`, `htubeBdM` and `hBdM`.
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

/-! ### The resolved cell over and away from the tube -/

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G cell : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

/-- Off the preimage of a set the resolved cell takes its values outside that set. This is the
unbundled form of `CrossSeamRegluedData.cell_notMem_tube`; it mentions no tube data, so it
applies at the parametrised cylinder, which is where the split is actually taken. -/
theorem notMem_tube_of_eqOn_compl (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' U))
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain \ ⇑G ⁻¹' U) : ⇑cell x ∉ U := by
  rw [hcompl hx]
  exact hx.2

namespace CrossSeamTubeData

/-- Over the parametrised cylinder a resolved cell covers exactly the parametrised replacement
figure. This is the unbundled form of `CrossSeamRegluedData.image_cell_tube`, restated without
that bundle so that the derivation of normality does not go through the very field it
removes. -/
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

/-- The resolution keeps the part of the source disk lying over the parametrised cylinder inside
that cylinder. This is the unbundled form of `CrossSeamRegluedData.mapsTo_cell_tube`. -/
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

/-- The resolution is injective over the parametrised cylinder: the two chord sheets are
disjoint. This is the unbundled form of `CrossSeamRegluedData.injOn_cell_tube`. -/
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

/-- **Every double point of the resolved cell is a double point of the reglued cell lying
outside the parametrised cylinder.** Over the cylinder the resolution is injective, and a value
taken in the cylinder is never taken again off it, so no double point survives in the cylinder
and no new one is created. This is the local form of
`CrossSeamRegluedData.doublePointSet_cell_eq` that the crossing condition consumes; unlike that
statement it needs no hypothesis on `G`. -/
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

/-! ### The resolved cell is a normal singular cell -/

/-- **The resolved cell of a cross seam resolution is again a normal singular cell.** The data
`hdomain`, `hcoord`, `hreglued`, `hresolved` and `hcompl` are exactly the geometric fields of
`CrossSeamRegluedData`, and `hdouble` is its conclusion
`CrossSeamRegluedData.doublePointSet_cell_eq`; the remaining hypotheses are the properties of
the reglued cell `G` and of the tube that the resolution uses.

Their content is:

* `hGinj`, `hGfiber`, `hGboundary`, `hGimage` : the four elementary fields of a normal singular
  cell for the reglued cell `G`, which is not itself asserted to be normal;
* `hGcrossing` : at each of its double points lying outside the tube, `G` has a normal double
  crossing in a chart whose source misses the parametrised model cylinder. The last clause is
  what makes the source set of the crossing condition unchanged by the resolution. The double
  points of the resolved cell are located off the *cylinder* by
  `doublePointSet_resolved_subset`, but `hdouble` together with
  `CrossSeamTubeData.doublePointSet_sdiff_branchCarrier` puts them off the whole tube, so this
  hypothesis does not have to be strengthened to the cylinder;
* `hendDisks` : the two end cross sections of the tube lie in the boundary surface `B`;
* `hends` : over the parametrised cylinder, a point of the source disk lies on the boundary of
  the source disk exactly when it lies over one of the two ends of the base interval, that is,
  the two source strips run from one end of the cylinder to the other;
* `htubeBdM` : the parametrised cylinder meets the boundary of the manifold only in its two end
  cross sections;
* `hBdM` : the surface `B` in which the boundary curve of the cell runs lies in the boundary
  `BdM` of the manifold. -/
noncomputable def normalOfResolvedCell (T : CrossSeamTubeData hD c U)
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
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
        Disjoint e.source (T.chart '' spliceCylinder) ∧
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
    obtain ⟨e, he, hye, hdis, hcross⟩ := hGcrossing y hyG hyU
    have hnot : ∀ x ∈ G.domain, ⇑G x ∈ e.source ∨ ⇑cell x ∈ e.source →
        ⇑G x ∉ T.chart '' spliceCylinder := by
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

/-! ### The normality of the resolved cell, in bundled form -/

namespace CrossSeamRegluedData

variable {T : CrossSeamTubeData hD c U}

/-- **The normality of the resolved cell of a `CrossSeamRegluedData`.** The structure carries no
`normal` field: that field has been deleted, and this is its producer. The proof passes only the
six geometric fields of `R` to `CrossSeamTubeData.normalOfResolvedCell`, so every consumer that
needs the normality of `R.cell` takes the output of `R.normalOfTube`, applied to the extra
hypotheses below, as an explicit argument. The hypothesis `hGD`, which says that the cross
reglue changes no double point outside the parametrised cylinder, is the one already consumed by
`CrossSeamRegluedData.doublePointSet_cell_eq`; the remaining hypotheses are described at
`CrossSeamTubeData.normalOfResolvedCell`. The end edge hypothesis `hends` is phrased through
`R.coord`, the model coordinate field of `R`, and not through a separately quantified
coordinate.

`hGD` is stated at the closed parametrised cylinder and not at the open tube `U`, and the tube
form does not imply it: it constrains nothing about the double points of `G` lying in `U` but
off the cylinder. Every other hypothesis is either unchanged or holds on the smaller set. -/
noncomputable def normalOfTube (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
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
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (R.coord x).2.2 = 0 ∨ (R.coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM) :
    NormalSingularCellData R.cell BdM B :=
  T.normalOfResolvedCell R.domain_eq R.bijOn_coord R.reglued_eq R.resolved_eq R.eqOn_compl
    (R.doublePointSet_cell_eq hGD) hGinj hGfiber hGboundary hGimage hGcrossing hendDisks
    hends htubeBdM hBdM

end CrossSeamRegluedData

end DifferentialGeometry.Topology.PiecewiseLinear
