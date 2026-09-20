/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

/-!
# The normal crossing product tube around a boundary branch

`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution` proves, purely
in the model, that replacing the two bent transverse arcs of the boundary cross reglue by the
two disjoint chords of the cross section square deletes the branch and changes nothing on the
four lateral attaching intervals. This file supplies the geometry that carries that model
computation back into the manifold, and the transport of the two double point conclusions of
`CrossSeamResolutionData`.

## The tube

`CrossSeamTubeCore chart figure double branch tube` is the purely model-level contract: an open
set `tube` of the manifold and a map `chart` of the model cylinder
`spliceCylinder = spliceSquare ×ˢ Icc 0 1` into the manifold which

* is continuous and injective on the closed model cylinder and lands in `tube`;
* carries the model core curve `spliceCore` exactly onto `branch`;
* carries the model crossing figure `crossingFigure`, that is the four half sheets of the
  transverse cross swept along the base interval, exactly onto the part `figure ∩ tube` of the
  image of the cell inside the tube;
* meets the singular set only in the branch: `double ∩ tube = branch`.

`CrossSeamTubeData hD c U` is that contract instantiated at the image, the double point set and
the carrier of the branch `c` of a normal singular cell. The base of the tube is an interval and
not a circle, so no period identification and no sheet exchange occur; this is the boundary
branch case.

`crossSeamTubeCore_spliceEmbedding` checks that the contract is not vacuous: the standard splice
cylinder sitting in `EuclideanSpace ℝ (Fin 3)` through a linear homeomorphism satisfies it, with
its core curve as the branch and the whole space as the tube, and
`spliceEmbedding_image_spliceCore_eq_inter` records that this core curve really is the
self-intersection of the two crossing sheets and not an arbitrary choice.

The full `CrossSeamTubeData` is *not* produced here for a given boundary branch. The missing
statement is isolated as `IsCrossSeamTubeProducer`; see the end of this file for its exact
content.

## The transport

`CrossSeamRegluedData T G` records how the cross reglued cell `G` of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` sits over the tube, together
with the resolved cell. Over the tube the reglued map is the model raw cross reglue
`crossSeamInclude` and the resolved map is the model chord resolution `crossSeamResolve`; away
from the tube the two maps agree.

From that data alone the following are proved.

* `CrossSeamRegluedData.doublePointSet_reglued_tube` : inside the tube the reglued cell still has
  the whole branch carrier as its double point set, which is the model form of the defect
  `hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain`.
* `CrossSeamRegluedData.doublePointSet_cell_tube` : inside the tube the resolved cell has no
  double point at all.
* `CrossSeamRegluedData.image_cell_inter_lateral` : on the lateral boundary of the tube the
  resolved image and the old image agree, so the replacement is glued in along the same curves.
* `CrossSeamRegluedData.doublePointSet_cell_eq` and `CrossSeamRegluedData.image_cell_subset` :
  the two double point fields of `CrossSeamResolutionData`.

`exists_resolved_cell_of_tube` is the resulting partial producer and
`crossSeamResolutionDataOfTube` upgrades it to a full `CrossSeamResolutionData` once the branch
correspondence is supplied.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-! ### Double point sets under composition -/

/-- Double point sets only depend on the values of the map on the set. -/
theorem doublePointSet_congr {X Y : Type*} {f g : X → Y} {P : Set X} (h : EqOn f g P) :
    doublePointSet f P = doublePointSet g P := by
  ext y
  constructor
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).symm.trans hfx, (h hz).symm.trans hfz⟩
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).trans hfx, (h hz).trans hfz⟩

/-- Reparametrising the source of a map by a bijection does not change its double point set. -/
theorem doublePointSet_comp_of_bijOn {X Y Z : Type*} {e : X → Y} {f : Y → Z} {P : Set X}
    {Q : Set Y} (he : BijOn e P Q) : doublePointSet (f ∘ e) P = doublePointSet f Q := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨e x, he.mapsTo hx, e z, he.mapsTo hz, fun h => hxz (he.injOn hx hz h), hfx, hfz⟩
  · rintro y ⟨a, ha, b, hb, hab, hfa, hfb⟩
    obtain ⟨x, hx, rfl⟩ := he.surjOn ha
    obtain ⟨z, hz, rfl⟩ := he.surjOn hb
    exact ⟨x, hx, z, hz, fun h => hab (congrArg e h), hfa, hfb⟩

/-- Postcomposing a map with a map injective on its image transports the double point set
forward. This is what lets a model computation of a double point set be read in the manifold
through an injective tube parametrisation. -/
theorem image_doublePointSet_of_injOn {X Y Z : Type*} {f : X → Y} {g : Y → Z} {P : Set X}
    (hg : InjOn g (f '' P)) : doublePointSet (g ∘ f) P = g '' doublePointSet f P := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    have h : f x = f z := hg ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩ (hfx.trans hfz.symm)
    exact ⟨f x, ⟨x, hx, z, hz, hxz, rfl, h.symm⟩, hfx⟩
  · rintro _ ⟨w, ⟨x, hx, z, hz, hxz, hfx, hfz⟩, rfl⟩
    exact ⟨x, hx, z, hz, hxz, congrArg g hfx, congrArg g hfz⟩

/-! ### The model figures lie in the model cylinder -/

/-- The core curve lies in the model cylinder. -/
theorem spliceCore_subset_spliceCylinder : spliceCore ⊆ spliceCylinder := by
  intro p hp
  refine ⟨?_, hp.2⟩
  have h : p.1 = ((0 : ℝ), (0 : ℝ)) := hp.1
  rw [h, mem_spliceSquare]
  norm_num

/-- The old crossing figure lies in the model cylinder. -/
theorem crossingFigure_subset_spliceCylinder : crossingFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

/-- The replacement figure lies in the model cylinder. -/
theorem spliceFigure_subset_spliceCylinder : spliceFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

/-- The figure of the raw cross reglue lies in the model cylinder. -/
theorem bentFigure_subset_spliceCylinder : bentFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨bentArcPos_subset_spliceSquare h, ht⟩
  · exact ⟨bentArcNeg_subset_spliceSquare h, ht⟩

/-- The lateral boundary of the model cylinder lies in the model cylinder. -/
theorem spliceSquareBoundary_prod_subset_spliceCylinder :
    spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 ⊆ spliceCylinder := by
  rintro p ⟨h, ht⟩
  exact ⟨h.1, ht⟩

/-! ### The contract of a normal crossing product tube -/

/-- **The normal crossing product tube, in model-level form.** `chart` parametrises a tube around
a branch of a singular surface by the model cylinder of
`DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice`, with `figure` the image of the
surface, `double` its double point set, `branch` the carrier of the branch being resolved and
`tube` the open set that the parametrisation fills.

Each field is one geometric fact:

* `isOpen_tube` : the tube is an open set of the manifold;
* `continuousOn_chart`, `injOn_chart` : the parametrisation is a topological embedding of the
  compact model cylinder;
* `image_subset_tube` : the parametrised cylinder lies in the tube;
* `image_spliceCore` : the model core curve is carried exactly onto the branch carrier;
* `image_crossingFigure` : the four model half sheets of the transverse cross, swept along the
  base interval, are carried exactly onto the part of the surface lying in the tube, so the tube
  is a normal crossing tube and not merely a neighbourhood;
* `double_inter_tube` : the tube meets the double point set only in the branch being resolved, so
  no other branch enters the tube.

The base of the model cylinder is the interval `Icc 0 1` and not a circle, so the tube is a
genuine product and no sheet exchange across a period can occur. This is the boundary branch
case; a closed branch would need the period identification `SpliceRel`. -/
structure CrossSeamTubeCore {M : Type u} [TopologicalSpace M] (chart : (ℝ × ℝ) × ℝ → M)
    (figure double branch tube : Set M) : Prop where
  /-- The tube is an open set of the manifold. -/
  isOpen_tube : IsOpen tube
  /-- The tube parametrisation is continuous on the closed model cylinder. -/
  continuousOn_chart : ContinuousOn chart spliceCylinder
  /-- The tube parametrisation is injective on the closed model cylinder. -/
  injOn_chart : InjOn chart spliceCylinder
  /-- The parametrised model cylinder lies in the tube. -/
  image_subset_tube : chart '' spliceCylinder ⊆ tube
  /-- The model core curve is carried exactly onto the branch carrier. -/
  image_spliceCore : chart '' spliceCore = branch
  /-- The four model half sheets, swept along the base interval, are exactly the part of the
  surface lying in the tube. -/
  image_crossingFigure : chart '' crossingFigure = figure ∩ tube
  /-- The tube meets the double point set only in the branch being resolved. -/
  double_inter_tube : double ∩ tube = branch

/-! ### The model satisfies the contract -/

/-- A linear homeomorphism of the ambient space `(ℝ × ℝ) × ℝ` of the model cylinder onto the
model space `EuclideanSpace ℝ (Fin 3)` of a piecewise linear three-manifold. -/
noncomputable def spliceEmbedding : ((ℝ × ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The core curve of the model cylinder really is the self-intersection of the two crossing
sheets, so taking it as the branch carrier in `crossSeamTubeCore_spliceEmbedding` is not an
arbitrary choice. -/
theorem spliceEmbedding_image_spliceCore_eq_inter :
    ⇑spliceEmbedding '' spliceCore =
      ⇑spliceEmbedding '' crossingSheetX ∩ ⇑spliceEmbedding '' crossingSheetY := by
  rw [← crossingSheetX_inter_crossingSheetY,
    Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _) (subset_univ _)]

/-- **The contract of a normal crossing product tube is not vacuous.** The standard splice
cylinder sitting in `EuclideanSpace ℝ (Fin 3)` satisfies it, with the crossing figure as the
surface, the core curve as both the double point set and the branch carrier, and the whole space
as the tube. -/
theorem crossSeamTubeCore_spliceEmbedding :
    CrossSeamTubeCore (M := EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding
      (⇑spliceEmbedding '' crossingFigure) (⇑spliceEmbedding '' spliceCore)
      (⇑spliceEmbedding '' spliceCore) univ where
  isOpen_tube := isOpen_univ
  continuousOn_chart := spliceEmbedding.continuous.continuousOn
  injOn_chart := spliceEmbedding.injective.injOn
  image_subset_tube := subset_univ _
  image_spliceCore := rfl
  image_crossingFigure := (Set.inter_univ _).symm
  double_inter_tube := Set.inter_univ _

/-! ### The tube of a boundary branch of a normal singular cell -/

/-- **The normal crossing product tube around a branch of a normal singular cell.** The tube
parametrisation `chart` satisfies the model-level contract `CrossSeamTubeCore` at the image of
the cell, its double point set and the carrier of the branch `c`.

No producer of this structure from a boundary branch is given here; see
`IsCrossSeamTubeProducer` for the exact missing statement. -/
structure CrossSeamTubeData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  /-- The tube parametrisation, defined on the model cylinder. -/
  chart : (ℝ × ℝ) × ℝ → M
  /-- The parametrisation is a normal crossing product tube around the branch `c`. -/
  isTube : CrossSeamTubeCore chart (D '' D.domain) (doublePointSet D D.domain)
    (hD.singularSet.branchCarrier c) U

namespace CrossSeamTubeData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

/-- The branch carrier lies in the tube. -/
theorem branchCarrier_subset_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ U := by
  rw [← T.isTube.image_spliceCore]
  exact (Set.image_mono spliceCore_subset_spliceCylinder).trans T.isTube.image_subset_tube

/-- The tube is a neighbourhood of the branch carrier. -/
theorem branchCarrier_subset_interior_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ interior U := by
  rw [T.isTube.isOpen_tube.interior_eq]
  exact T.branchCarrier_subset_tube

/-- The parametrised model cylinder is compact, hence so is the branch carrier. -/
theorem isCompact_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    IsCompact (T.chart '' spliceCylinder) :=
  isHPolytope_spliceCylinder.isPolyhedron.isCompact.image_of_continuousOn
    T.isTube.continuousOn_chart

/-- **Deleting the branch is deleting the tube.** Since the tube meets the double point set only
in the branch, removing the branch carrier from the double point set is the same as removing the
whole tube. This is what turns the local statement proved inside the tube into the global form
required by `CrossSeamResolutionData.doublePointSet_eq`. -/
theorem doublePointSet_sdiff_branchCarrier (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ U := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hyU => hyb ?_⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, hyU⟩
  · rintro y ⟨hy, hyU⟩
    exact ⟨hy, fun hyb => hyU (T.branchCarrier_subset_tube hyb)⟩

end CrossSeamTubeData

/-! ### The cross reglued cell in the normal form of the tube -/

/-- **The cross reglued cell and its resolution, read in the tube.** The cell `G` is the cross
reglued cell of `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`, whose two
new seams still meet at the centre of the transverse cross.

Each field is one geometric fact:

* `cell`, `domain_eq` : the resolution is a new map on the same source disk, not a
  reparametrisation of `G` and not an ambient postcomposition, either of which would preserve
  every coincidence of values and so could never delete a branch;
* `coord`, `bijOn_coord` : the part of the source disk lying over the tube is two strips,
  identified with the two model strips `bentSource`;
* `reglued_eq` : over the tube the reglued map is the model raw cross reglue
  `crossSeamInclude`, that is, each strip is sent to its bent transverse sheet;
* `resolved_eq` : over the tube the resolved map is the model chord resolution
  `crossSeamResolve`, that is, each strip is sent to its chord sheet;
* `eqOn_compl` : away from the tube the resolution changes nothing;
* `normal` : the resolved cell is again a normal singular cell over the same boundary data. -/
structure CrossSeamRegluedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) (G : SingularTwoCell M) where
  /-- The resolved singular two cell. -/
  cell : SingularTwoCell M
  /-- The resolution keeps the source disk of the reglued cell. -/
  domain_eq : cell.domain = G.domain
  /-- The model coordinate on the part of the source disk lying over the tube. -/
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  /-- The part of the source disk lying over the tube is carried bijectively onto the two model
  strips of the raw cross reglue. -/
  bijOn_coord : BijOn coord (G.domain ∩ ⇑G ⁻¹' U) bentSource
  /-- Over the tube the reglued map is the model raw cross reglue. -/
  reglued_eq : EqOn G (T.chart ∘ crossSeamInclude ∘ coord) (G.domain ∩ ⇑G ⁻¹' U)
  /-- Over the tube the resolved map is the model chord resolution. -/
  resolved_eq : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord) (G.domain ∩ ⇑G ⁻¹' U)
  /-- Away from the tube the resolution changes nothing. -/
  eqOn_compl : EqOn cell G (G.domain \ ⇑G ⁻¹' U)
  /-- The resolved cell is again a normal singular cell over the same boundary data. -/
  normal : NormalSingularCellData cell BdM B

namespace CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

/-- Over the tube the resolved cell covers exactly the parametrised replacement figure. -/
theorem image_cell_tube (R : CrossSeamRegluedData T G) :
    R.cell '' (G.domain ∩ ⇑G ⁻¹' U) = T.chart '' spliceFigure := by
  have h : R.cell '' (G.domain ∩ ⇑G ⁻¹' U)
      = (T.chart ∘ crossSeamResolve ∘ R.coord) '' (G.domain ∩ ⇑G ⁻¹' U) :=
    Set.image_congr fun x hx => R.resolved_eq hx
  rw [h, Set.image_comp, Set.image_comp, R.bijOn_coord.image_eq, image_crossSeamResolve]

/-- The resolution keeps the part of the source disk lying over the tube inside the tube: the
chords of the cross section square never leave the cross section. -/
theorem mapsTo_cell_tube (R : CrossSeamRegluedData T G) :
    MapsTo R.cell (G.domain ∩ ⇑G ⁻¹' U) U := by
  intro x hx
  have h : R.cell x ∈ R.cell '' (G.domain ∩ ⇑G ⁻¹' U) := ⟨x, hx, rfl⟩
  rw [R.image_cell_tube] at h
  exact T.isTube.image_subset_tube (Set.image_mono spliceFigure_subset_spliceCylinder h)

/-- **The resolution is injective over the tube.** This is the model theorem
`injOn_crossSeamResolve`, that the two chord sheets are disjoint, read through the tube. -/
theorem injOn_cell_tube (R : CrossSeamRegluedData T G) :
    InjOn R.cell (G.domain ∩ ⇑G ⁻¹' U) := by
  intro x hx z hz hxz
  have hxm : R.coord x ∈ bentSource := R.bijOn_coord.mapsTo hx
  have hzm : R.coord z ∈ bentSource := R.bijOn_coord.mapsTo hz
  have hxs : crossSeamResolve (R.coord x) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hxm, rfl⟩
  have hzs : crossSeamResolve (R.coord z) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hzm, rfl⟩
  rw [R.resolved_eq hx, R.resolved_eq hz] at hxz
  simp only [Function.comp_apply] at hxz
  have hmodel : crossSeamResolve (R.coord x) = crossSeamResolve (R.coord z) :=
    T.isTube.injOn_chart (spliceFigure_subset_spliceCylinder hxs)
      (spliceFigure_subset_spliceCylinder hzs) hxz
  exact R.bijOn_coord.injOn hx hz (injOn_crossSeamResolve hxm hzm hmodel)

/-- **The resolved cell has no double point inside the tube.** This is the exact model statement
`doublePointSet_crossSeamResolve` read through the tube. -/
theorem doublePointSet_cell_tube (R : CrossSeamRegluedData T G) :
    doublePointSet R.cell (G.domain ∩ ⇑G ⁻¹' U) = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr R.injOn_cell_tube

/-- **The raw cross reglue still has the whole branch as its double point set inside the tube.**
This is the model statement `doublePointSet_crossSeamInclude` read through the tube, and it is
the defect `hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain` of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` in local form. -/
theorem doublePointSet_reglued_tube (R : CrossSeamRegluedData T G) :
    doublePointSet G (G.domain ∩ ⇑G ⁻¹' U) = hD.singularSet.branchCarrier c := by
  have hinj : InjOn T.chart (crossSeamInclude '' bentSource) := by
    rw [image_crossSeamInclude]
    exact T.isTube.injOn_chart.mono bentFigure_subset_spliceCylinder
  have hcongr : doublePointSet G (G.domain ∩ ⇑G ⁻¹' U)
      = doublePointSet ((T.chart ∘ crossSeamInclude) ∘ R.coord) (G.domain ∩ ⇑G ⁻¹' U) :=
    doublePointSet_congr R.reglued_eq
  rw [hcongr, doublePointSet_comp_of_bijOn R.bijOn_coord,
    image_doublePointSet_of_injOn hinj, doublePointSet_crossSeamInclude,
    T.isTube.image_spliceCore]

/-- Away from the tube the resolved cell takes its values outside the tube. -/
theorem cell_notMem_tube (R : CrossSeamRegluedData T G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ G.domain \ ⇑G ⁻¹' U) : R.cell x ∉ U := by
  rw [R.eqOn_compl hx]
  exact hx.2

/-- Every point of the source disk either lies over the tube or does not. -/
theorem mem_tube_or_notMem_tube (G : SingularTwoCell M) (U : Set M)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain) :
    x ∈ G.domain ∩ ⇑G ⁻¹' U ∨ x ∈ G.domain \ ⇑G ⁻¹' U := by
  by_cases h : G x ∈ U
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

/-- **The resolution deletes exactly the branch.** The hypothesis `hGD` is the statement that the
cross reglue itself changes no double point outside the tube; it is a property of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` and not of the seam
resolution, and it is not proved here. -/
theorem doublePointSet_cell_eq (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ U = doublePointSet D D.domain \ U) :
    doublePointSet R.cell R.cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  rw [T.doublePointSet_sdiff_branchCarrier, ← hGD, R.domain_eq]
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
    rcases mem_tube_or_notMem_tube G U hx with hxV | hxW <;>
      rcases mem_tube_or_notMem_tube G U hz with hzV | hzW
    · exact absurd (R.injOn_cell_tube hxV hzV (hyx.trans hyz.symm)) hxz
    · exfalso
      have h1 : y ∈ U := by rw [← hyx]; exact R.mapsTo_cell_tube hxV
      have h2 : y ∉ U := by rw [← hyz]; exact R.cell_notMem_tube hzW
      exact h2 h1
    · exfalso
      have h1 : y ∈ U := by rw [← hyz]; exact R.mapsTo_cell_tube hzV
      have h2 : y ∉ U := by rw [← hyx]; exact R.cell_notMem_tube hxW
      exact h2 h1
    · refine ⟨⟨x, hx, z, hz, hxz, ?_, ?_⟩, ?_⟩
      · rw [← R.eqOn_compl hxW]; exact hyx
      · rw [← R.eqOn_compl hzW]; exact hyz
      · rw [← hyx]; exact R.cell_notMem_tube hxW
  · rintro y ⟨⟨x, hx, z, hz, hxz, hyx, hyz⟩, hyU⟩
    have hxU : G x ∉ U := by rw [hyx]; exact hyU
    have hzU : G z ∉ U := by rw [hyz]; exact hyU
    exact ⟨x, hx, z, hz, hxz, (R.eqOn_compl ⟨hx, hxU⟩).trans hyx,
      (R.eqOn_compl ⟨hz, hzU⟩).trans hyz⟩

/-- **The resolved image stays inside the old image together with the tube.** The resolved map is
not a reparametrisation of the reglued map, so its image is in general not contained in the old
image; the excess is confined to the tube. -/
theorem image_cell_subset (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain) :
    R.cell '' R.cell.domain ⊆ D '' D.domain ∪ U := by
  rw [R.domain_eq]
  rintro _ ⟨x, hx, rfl⟩
  rcases mem_tube_or_notMem_tube G U hx with hxV | hxW
  · exact Or.inr (R.mapsTo_cell_tube hxV)
  · exact Or.inl (hGim ⟨x, hx, (R.eqOn_compl hxW).symm⟩)

/-- **The replacement is glued in along the same curves.** On the lateral boundary of the tube
the resolved image and the old image agree, because the two bent arcs and the two chords have the
same lateral trace. -/
theorem image_cell_inter_lateral (R : CrossSeamRegluedData T G) :
    R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) =
      D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
  have hlat : T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) ⊆ U :=
    (Set.image_mono spliceSquareBoundary_prod_subset_spliceCylinder).trans
      T.isTube.image_subset_tube
  have hleft : R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = T.chart '' spliceFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
      rw [R.domain_eq] at hx
      rcases mem_tube_or_notMem_tube G U hx with hxV | hxW
      · refine ⟨?_, hy⟩
        rw [← R.image_cell_tube]
        exact ⟨x, hxV, rfl⟩
      · exact absurd (hlat hy) (R.cell_notMem_tube hxW)
    · rintro y ⟨hy1, hy2⟩
      rw [← R.image_cell_tube] at hy1
      obtain ⟨x, hx, rfl⟩ := hy1
      exact ⟨⟨x, by rw [R.domain_eq]; exact hx.1, rfl⟩, hy2⟩
  have hright : D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = T.chart '' crossingFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
    rw [T.isTube.image_crossingFigure]
    apply Subset.antisymm
    · rintro y ⟨hy1, hy2⟩
      exact ⟨⟨hy1, hlat hy2⟩, hy2⟩
    · rintro y ⟨⟨hy1, -⟩, hy2⟩
      exact ⟨hy1, hy2⟩
  rw [hleft, hright,
    ← Set.InjOn.image_inter T.isTube.injOn_chart spliceFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    ← Set.InjOn.image_inter T.isTube.injOn_chart crossingFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    crossingFigure_inter_lateral_eq_spliceFigure_inter_lateral]

end CrossSeamRegluedData

/-! ### The partial producer of the resolved cell -/

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

/-- **The two double point conclusions of the cross seam resolution.** Given a normal crossing
product tube around the branch `c` and the cross reglued cell `G` read in the normal form of that
tube, the resolved cell is again normal, its double point set is exactly the old one with the
carrier of `c` removed, and its image stays inside the old image together with the tube.

The hypotheses that are not proved here are `hGim`, which is a conclusion of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`, and `hGD`, which says that
the cross reglue changes no double point outside the tube.

The two remaining fields of `CrossSeamResolutionData`, the branch correspondence and its
compatibility with branch carriers, are supplied separately in
`crossSeamResolutionDataOfTube`. -/
theorem exists_resolved_cell_of_tube (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ U = doublePointSet D D.domain \ U) :
    ∃ (cell : SingularTwoCell M) (_hcell : NormalSingularCellData cell BdM B),
      doublePointSet cell cell.domain =
          doublePointSet D D.domain \ hD.singularSet.branchCarrier c ∧
        cell '' cell.domain ⊆ D '' D.domain ∪ U :=
  ⟨R.cell, R.normal, R.doublePointSet_cell_eq hGD, R.image_cell_subset hGim⟩

/-- **The full contract of a geometric cross seam resolution.** The two double point fields come
from the tube by `exists_resolved_cell_of_tube`; the branch correspondence `e` and its
compatibility `he` with branch carriers are taken as hypotheses, since they belong to the
combinatorics of the resolved triangulation rather than to the seam resolution. -/
def crossSeamResolutionDataOfTube (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ U = doublePointSet D D.domain \ U)
    (e : R.normal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, R.normal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    CrossSeamResolutionData hD c U where
  cell := R.cell
  normal := R.normal
  doublePointSet_eq := R.doublePointSet_cell_eq hGD
  branchEquiv := e
  branchCarrier_eq := he
  image_subset := R.image_cell_subset hGim

/-- **The complexity drops strictly.** The descent that Moise's induction consumes, obtained from
the tube together with the branch correspondence. -/
theorem complexity_lt_of_tube (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ U = doublePointSet D D.domain \ U)
    (e : R.normal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, R.normal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    R.normal.singularSet.complexity < hD.singularSet.complexity :=
  (crossSeamResolutionDataOfTube R hGim hGD e he).complexity_lt

/-! ### The statement that is not proved -/

/-- **The relative regular neighbourhood statement that would produce the tube.** For every
normal singular cell and every boundary branch of its singular set there is an open set `U` of
the manifold and a normal crossing product tube `CrossSeamTubeData hD c U` around that branch.

Unfolding `CrossSeamTubeCore`, this asks for a parametrisation of a neighbourhood of the branch
carrier by the model cylinder `spliceSquare ×ˢ Icc 0 1` which carries the core `{(0, 0)} ×ˢ
Icc 0 1` onto the branch carrier and the four half sheets of the transverse cross, swept along
the base interval, onto the part of the surface lying in the neighbourhood, and whose
neighbourhood meets the double point set in that branch only.

The existence of *some* piecewise linear ball neighbourhood of a branch arc is available from the
regular neighbourhood layer of the tree; what is missing is the product structure of that ball
*relative to the four local sheets of the cell*, which is a relative regular neighbourhood
statement and does not follow from the absolute one. -/
def IsCrossSeamTubeProducer (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  ∀ (D : SingularTwoCell M) (BdM B : Set M) (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
    ∃ U : Set M, Nonempty (CrossSeamTubeData hD c U)

end DifferentialGeometry.Topology.PiecewiseLinear
