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
  transverse cross swept along the base interval, exactly onto the part
  `figure ∩ chart '' spliceCylinder` of the surface lying in the parametrised cylinder;
* meets the singular set only in the branch: `double ∩ tube = branch`.

The third clause compares the surface with the *closed* parametrised cylinder, exactly as
`IsCylindricalDiagram.image_eq` does, and not with the open set `tube`. Comparing it with the
tube, as `chart '' crossingFigure = figure ∩ tube`, makes the contract uninhabited over a
Hausdorff manifold: the left side is a continuous image of a compact set, hence closed, while
the right side is relatively open in `figure`, so a connected surface meeting the tube would
have to be swallowed by it whole, `double` would collapse onto `branch`, and the complexity
could never exceed one. The open set `tube` is kept only in the two clauses that need a
neighbourhood, `image_subset_tube` and `double_inter_tube`; every clause that compares two
figures now compares two compact sets.

`CrossSeamTubeData hD c U` is that contract instantiated at the image, the double point set and
the carrier of the branch `c` of a normal singular cell. The base of the tube is an interval and
not a circle, so no period identification and no sheet exchange occur; this is the boundary
branch case.

`crossSeamTubeCore_spliceEmbedding` checks that the contract is not vacuous, and that it is not
vacuous in a *degenerate* configuration: the witness surface `tubeWitnessSurface` runs out of
the far end of the tube and carries a second crossing curve outside the tube, so neither of the
two collapses forced by the old clause occurs. The two facts are recorded separately as
`spliceEmbedding_image_crossingFigure_ssubset_surface`,
`spliceEmbedding_surface_not_subset_tube` and
`spliceEmbedding_image_spliceCore_ssubset_double`. That the two curves of the witness double
point set really are the self-intersections of the witness sheets, and not an arbitrary choice,
is `spliceEmbedding_image_spliceCore_eq_inter`, `tubeWitnessSheetX_inter_crossingSheetY`,
`tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY` and
`disjoint_tubeWitnessNear_tubeWitnessFar`.

The full `CrossSeamTubeData` is *not* produced here for a given boundary branch. The missing
statement is isolated as `IsCrossSeamTubeProducer`; see the end of this file for its exact
content.

## The transport

`CrossSeamRegluedData T G` records how the cross reglued cell `G` of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` sits over the tube, together
with the resolved cell. Over the parametrised cylinder `T.chart '' spliceCylinder` the reglued
map is the model raw cross reglue `crossSeamInclude` and the resolved map is the model chord
resolution `crossSeamResolve`; away from it the two maps agree.

The source of the cell is split along the closed parametrised cylinder and not along the open
`U`, for the same reason. `bijOn_coord` together with `reglued_eq` computes
`⇑G '' G.domain ∩ V` as the compact set `T.chart '' bentFigure`, so with `V := U` open that
intersection would again be compact and relatively open in a connected image, forcing the whole
reglued cell to sit inside one tube. With `V := T.chart '' spliceCylinder` both sides are
compact and the obstruction disappears. The passage from that closed set back to the open `U`,
which `CrossSeamResolutionData` still uses, is `CrossSeamTubeData.image_subset_tube` together
with `CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder`.

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
  base interval, are carried exactly onto the part of the surface lying in the parametrised
  cylinder, so the parametrisation is a normal crossing tube and not merely a neighbourhood;
* `double_inter_tube` : the tube meets the double point set only in the branch being resolved, so
  no other branch enters the tube.

The surface clause is stated against the closed set `chart '' spliceCylinder` and not against
`tube`. Against `tube` it would equate a compact set with a set relatively open in the surface,
which no normal crossing over a Hausdorff manifold satisfies; see the module docstring.

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
  surface lying in the parametrised cylinder. Both sides are compact; comparing them with the
  open `tube` instead would make the contract uninhabited. -/
  image_crossingFigure : chart '' crossingFigure = figure ∩ chart '' spliceCylinder
  /-- The tube meets the double point set only in the branch being resolved. -/
  double_inter_tube : double ∩ tube = branch

/-! ### The model satisfies the contract -/

/-- A linear homeomorphism of the ambient space `(ℝ × ℝ) × ℝ` of the model cylinder onto the
model space `EuclideanSpace ℝ (Fin 3)` of a piecewise linear three-manifold. -/
noncomputable def spliceEmbedding : ((ℝ × ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-! ### A non-degenerate witness -/

/-- The long transverse sheet of the witness: the cross section `x = 0` swept along `Icc 0 2`
rather than `Icc 0 1`, so that the surface runs out of the far end of the tube. -/
def tubeWitnessSheetX : Set ((ℝ × ℝ) × ℝ) := crossingArcX ×ˢ Icc (0 : ℝ) 2

/-- The cross section of the first sheet of the second crossing of the witness surface: the
vertical segment through `(4, 4)`, far away from the square of the model cylinder. -/
def tubeWitnessFarArcX : Set (ℝ × ℝ) := ({(4 : ℝ)} : Set ℝ) ×ˢ Icc (3 : ℝ) 5

/-- The cross section of the second sheet of the second crossing of the witness surface: the
horizontal segment through `(4, 4)`. -/
def tubeWitnessFarArcY : Set (ℝ × ℝ) := Icc (3 : ℝ) 5 ×ˢ ({(4 : ℝ)} : Set ℝ)

/-- The first sheet of the second crossing of the witness surface. -/
def tubeWitnessFarSheetX : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcX ×ˢ Icc (0 : ℝ) 1

/-- The second sheet of the second crossing of the witness surface. -/
def tubeWitnessFarSheetY : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcY ×ˢ Icc (0 : ℝ) 1

/-- The second double curve of the witness surface: the axis of the second crossing. It lies
outside the witness tube, so the witness has two double curves and not one. -/
def tubeWitnessFarCore : Set ((ℝ × ℝ) × ℝ) :=
  ({((4 : ℝ), (4 : ℝ))} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1

/-- The witness surface: the transverse cross of the model with its sheet `x = 0` prolonged
past the far end of the tube, together with a second crossing placed outside the tube. -/
def tubeWitnessSurface : Set ((ℝ × ℝ) × ℝ) :=
  tubeWitnessSheetX ∪ crossingSheetY ∪ tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY

/-- The double point set of the witness surface: the core of the model cylinder together with
the axis of the second crossing. -/
def tubeWitnessDouble : Set ((ℝ × ℝ) × ℝ) := spliceCore ∪ tubeWitnessFarCore

/-- The witness tube: an open box around the model cylinder, small enough to miss both the
second crossing and the far end of the prolonged sheet. -/
def tubeWitnessTube : Set ((ℝ × ℝ) × ℝ) :=
  (Ioo (-2 : ℝ) 2 ×ˢ Ioo (-2 : ℝ) 2) ×ˢ Ioo (-1 : ℝ) 2

/-- The two cross sections of the second crossing meet in the single point `(4, 4)`. -/
theorem tubeWitnessFarArcX_inter_tubeWitnessFarArcY :
    tubeWitnessFarArcX ∩ tubeWitnessFarArcY = {((4 : ℝ), (4 : ℝ))} := by
  ext p
  simp only [tubeWitnessFarArcX, tubeWitnessFarArcY, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h2⟩
    exact Prod.ext h1 h2
  · rintro rfl
    norm_num

/-- The second crossing of the witness surface meets itself exactly along its own axis, so the
second double curve is not an arbitrary choice. -/
theorem tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY :
    tubeWitnessFarSheetX ∩ tubeWitnessFarSheetY = tubeWitnessFarCore := by
  rw [tubeWitnessFarSheetX, tubeWitnessFarSheetY, Set.prod_inter_prod, Set.inter_self,
    tubeWitnessFarArcX_inter_tubeWitnessFarArcY, tubeWitnessFarCore]

/-- The prolonged sheet `x = 0` and the sheet `y = 0` still meet exactly along the core of the
model cylinder, so prolonging one sheet creates no double point beyond the end of the tube. -/
theorem tubeWitnessSheetX_inter_crossingSheetY :
    tubeWitnessSheetX ∩ crossingSheetY = spliceCore := by
  have h : Icc (0 : ℝ) 2 ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 :=
    Set.inter_eq_right.mpr (Set.Icc_subset_Icc le_rfl (by norm_num))
  rw [tubeWitnessSheetX, crossingSheetY, Set.prod_inter_prod, crossingArcX_inter_crossingArcY,
    h, spliceCore]

/-- The cross section of the second crossing misses the square of the model cylinder. -/
theorem disjoint_tubeWitnessFarArc_spliceSquare :
    Disjoint (tubeWitnessFarArcX ∪ tubeWitnessFarArcY) spliceSquare := by
  rw [Set.disjoint_left]
  rintro q (h | h) hq
  · rw [mem_spliceSquare] at hq
    have h4 : q.1 = 4 := h.1
    linarith [hq.1.2]
  · rw [mem_spliceSquare] at hq
    have h4 : q.2 = 4 := h.2
    linarith [hq.2.2]

/-- The two crossings of the witness surface are disjoint, so each contributes exactly one
double curve to `tubeWitnessDouble`. -/
theorem disjoint_tubeWitnessNear_tubeWitnessFar :
    Disjoint (tubeWitnessSheetX ∪ crossingSheetY)
      (tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY) := by
  rw [Set.disjoint_left]
  intro p hnear hfar
  have hsq : p.1 ∈ spliceSquare := by
    rcases hnear with h | h
    · exact h.1.1
    · exact h.1.1
  have hfarArc : p.1 ∈ tubeWitnessFarArcX ∪ tubeWitnessFarArcY := by
    rcases hfar with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  exact Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare hfarArc hsq

/-- Inside the model cylinder the witness surface is exactly the old crossing figure: both the
prolongation and the second crossing lie outside the cylinder. -/
theorem tubeWitnessSurface_inter_spliceCylinder :
    tubeWitnessSurface ∩ spliceCylinder = crossingFigure := by
  ext p
  constructor
  · rintro ⟨((h | h) | h) | h, hcyl⟩
    · exact ⟨Or.inl h.1, hcyl.2⟩
    · exact ⟨Or.inr h.1, h.2⟩
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inl h.1))
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inr h.1))
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩)), h.1, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inr ⟨h, ht⟩)), h.1, ht⟩

/-- The old crossing figure is part of the witness surface. -/
theorem crossingFigure_subset_tubeWitnessSurface : crossingFigure ⊆ tubeWitnessSurface := by
  rintro p ⟨h | h, ht⟩
  · exact Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨h, ht⟩))

/-- The core of the model cylinder is part of the witness double point set. -/
theorem spliceCore_subset_tubeWitnessDouble : spliceCore ⊆ tubeWitnessDouble :=
  Set.subset_union_left

/-- The model cylinder lies in the witness tube, which is therefore a neighbourhood of it. -/
theorem spliceCylinder_subset_tubeWitnessTube : spliceCylinder ⊆ tubeWitnessTube := by
  rintro p ⟨hsq, ht⟩
  rw [mem_spliceSquare] at hsq
  rw [Set.mem_Icc] at ht
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> constructor <;>
    linarith [hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2, ht.1, ht.2]

/-- The witness tube is open. -/
theorem isOpen_tubeWitnessTube : IsOpen tubeWitnessTube :=
  (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo

/-- The witness tube meets the witness double point set exactly in the core of the model
cylinder: the second double curve stays outside the tube. -/
theorem tubeWitnessDouble_inter_tubeWitnessTube :
    tubeWitnessDouble ∩ tubeWitnessTube = spliceCore := by
  apply Subset.antisymm
  · rintro p ⟨hd | hd, hu⟩
    · exact hd
    · exfalso
      have h4 : p.1 = ((4 : ℝ), (4 : ℝ)) := hd.1
      have hlt : p.1.1 < 2 := hu.1.1.2
      rw [h4] at hlt
      norm_num at hlt
  · intro p hp
    exact ⟨Or.inl hp,
      spliceCylinder_subset_tubeWitnessTube (spliceCore_subset_spliceCylinder hp)⟩

/-- The witness surface reaches past the far end of the tube. -/
theorem tubeWitnessTop_mem_surface :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∈ tubeWitnessSurface := by
  refine Or.inl (Or.inl (Or.inl ⟨⟨?_, rfl⟩, ?_⟩))
  · rw [mem_spliceSquare]
    norm_num
  · rw [Set.mem_Icc]
    norm_num

/-- That point of the witness surface is not on the old crossing figure. -/
theorem tubeWitnessTop_notMem_crossingFigure :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ crossingFigure := by
  rintro ⟨-, ht⟩
  rw [Set.mem_Icc] at ht
  norm_num at ht

/-- That point of the witness surface is not in the witness tube either. -/
theorem tubeWitnessTop_notMem_tube :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ tubeWitnessTube := by
  intro h
  have h2 : (((0 : ℝ), (0 : ℝ)), (2 : ℝ)).2 < 2 := h.2.2
  norm_num at h2

/-- The second double curve of the witness really is a double point of the witness. -/
theorem tubeWitnessFar_mem_double :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∈ tubeWitnessDouble := by
  refine Or.inr ⟨rfl, ?_⟩
  rw [Set.mem_Icc]
  norm_num

/-- The second double curve of the witness is not the branch carrier. -/
theorem tubeWitnessFar_notMem_spliceCore :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∉ spliceCore := by
  rintro ⟨h, -⟩
  have h4 : ((4 : ℝ), (4 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := h
  rw [Prod.mk.injEq] at h4
  norm_num at h4

/-- A strict inclusion of model sets stays strict in `EuclideanSpace ℝ (Fin 3)`, because the
model is placed there by an injection. The point `p` is the one that separates the two sets. -/
theorem spliceEmbedding_image_ssubset {s t : Set ((ℝ × ℝ) × ℝ)} (hst : s ⊆ t)
    {p : (ℝ × ℝ) × ℝ} (hpt : p ∈ t) (hps : p ∉ s) :
    ⇑spliceEmbedding '' s ⊂ ⇑spliceEmbedding '' t := by
  rw [Set.ssubset_iff_of_subset (Set.image_mono hst)]
  refine ⟨spliceEmbedding p, ⟨p, hpt, rfl⟩, ?_⟩
  rintro ⟨q, hq, hqe⟩
  have hqp : q = p := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact hps hq

/-- The core curve of the model cylinder really is the self-intersection of the two sheets of
the witness surface that cross inside the tube, so taking it as the branch carrier in
`crossSeamTubeCore_spliceEmbedding` is not an arbitrary choice. -/
theorem spliceEmbedding_image_spliceCore_eq_inter :
    ⇑spliceEmbedding '' spliceCore =
      ⇑spliceEmbedding '' tubeWitnessSheetX ∩ ⇑spliceEmbedding '' crossingSheetY := by
  rw [← tubeWitnessSheetX_inter_crossingSheetY,
    Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _) (subset_univ _)]

-- Non-degenerate: the surface leaves the tube through the far end and carries a second double
-- curve outside the tube, so neither of the two collapses forced by the old clause occurs.
/-- **The contract of a normal crossing product tube is not vacuous, and not vacuous only in
the degenerate configuration.** The witness lives in `EuclideanSpace ℝ (Fin 3)` through the
linear homeomorphism `spliceEmbedding`. Its surface is the transverse cross with one sheet
prolonged past the far end of the tube and a second crossing outside the tube, so
`spliceEmbedding_image_crossingFigure_ssubset_surface` and
`spliceEmbedding_surface_not_subset_tube` hold; its double point set carries the axis of that
second crossing, so `spliceEmbedding_image_spliceCore_ssubset_double` holds and the ambient
configuration has two double curves, not one. A descent from it is therefore not the trivial
one. -/
theorem crossSeamTubeCore_spliceEmbedding :
    CrossSeamTubeCore (M := EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding
      (⇑spliceEmbedding '' tubeWitnessSurface) (⇑spliceEmbedding '' tubeWitnessDouble)
      (⇑spliceEmbedding '' spliceCore) (⇑spliceEmbedding '' tubeWitnessTube) where
  isOpen_tube := by
    have h : IsOpen (⇑spliceEmbedding.toHomeomorph '' tubeWitnessTube) :=
      spliceEmbedding.toHomeomorph.isOpenMap _ isOpen_tubeWitnessTube
    exact h
  continuousOn_chart := spliceEmbedding.continuous.continuousOn
  injOn_chart := spliceEmbedding.injective.injOn
  image_subset_tube := Set.image_mono spliceCylinder_subset_tubeWitnessTube
  image_spliceCore := rfl
  image_crossingFigure := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _)
      (subset_univ _), tubeWitnessSurface_inter_spliceCylinder]
  double_inter_tube := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (subset_univ _)
      (subset_univ _), tubeWitnessDouble_inter_tubeWitnessTube]

/-- **The witness surface is strictly larger than the parametrised crossing figure.** Under the
refuted form of `image_crossingFigure` this was impossible, since the crossing figure would have
exhausted the whole connected surface. -/
theorem spliceEmbedding_image_crossingFigure_ssubset_surface :
    ⇑spliceEmbedding '' crossingFigure ⊂ ⇑spliceEmbedding '' tubeWitnessSurface :=
  spliceEmbedding_image_ssubset crossingFigure_subset_tubeWitnessSurface
    tubeWitnessTop_mem_surface tubeWitnessTop_notMem_crossingFigure

/-- **There is witness surface outside the witness tube.** This is the sharper form of the
previous statement: the surface is not merely larger than the crossing figure, it leaves the
tube altogether. -/
theorem spliceEmbedding_surface_not_subset_tube :
    ¬⇑spliceEmbedding '' tubeWitnessSurface ⊆ ⇑spliceEmbedding '' tubeWitnessTube := by
  intro h
  obtain ⟨q, hq, hqe⟩ := h ⟨_, tubeWitnessTop_mem_surface, rfl⟩
  have hqp : q = (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact tubeWitnessTop_notMem_tube hq

/-- **The witness double point set is strictly larger than the branch carrier.** So the ambient
configuration of the witness has a second double curve: a descent from it deletes one of two
branches, not the only one. -/
theorem spliceEmbedding_image_spliceCore_ssubset_double :
    ⇑spliceEmbedding '' spliceCore ⊂ ⇑spliceEmbedding '' tubeWitnessDouble :=
  spliceEmbedding_image_ssubset spliceCore_subset_tubeWitnessDouble
    tubeWitnessFar_mem_double tubeWitnessFar_notMem_spliceCore

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

/-- The branch carrier lies in the parametrised cylinder, being the image of its core curve. -/
theorem branchCarrier_subset_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ T.chart '' spliceCylinder := by
  rw [← T.isTube.image_spliceCore]
  exact Set.image_mono spliceCore_subset_spliceCylinder

/-- The branch carrier lies in the tube. -/
theorem branchCarrier_subset_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ U :=
  T.branchCarrier_subset_image_spliceCylinder.trans T.isTube.image_subset_tube

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

/-- **The parametrised cylinder meets the double point set only in the branch.** This is the
closed form of `double_inter_tube`: the branch carrier already lies in the cylinder, and the
cylinder lies in the tube, so nothing is lost by shrinking the tube to the cylinder. It is this
form that the transport of the model computation uses, because both sides of it are compact. -/
theorem doublePointSet_inter_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain ∩ T.chart '' spliceCylinder =
      hD.singularSet.branchCarrier c := by
  apply Subset.antisymm
  · rintro y ⟨hy, hcyl⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, T.isTube.image_subset_tube hcyl⟩
  · intro y hy
    refine ⟨?_, T.branchCarrier_subset_image_spliceCylinder hy⟩
    rw [← T.isTube.double_inter_tube] at hy
    exact hy.1

/-- **Deleting the branch is deleting the parametrised cylinder.** The closed counterpart of
`doublePointSet_sdiff_branchCarrier`, and the one the transport uses, since the source of the
cell is split along the parametrised cylinder and not along the tube. -/
theorem doublePointSet_sdiff_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ T.chart '' spliceCylinder := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hcyl => hyb ?_⟩
    rw [← T.doublePointSet_inter_image_spliceCylinder]
    exact ⟨hy, hcyl⟩
  · rintro y ⟨hy, hcyl⟩
    exact ⟨hy, fun hyb => hcyl (T.branchCarrier_subset_image_spliceCylinder hyb)⟩

end CrossSeamTubeData

/-! ### The cross reglued cell in the normal form of the tube -/

/-- **The cross reglued cell and its resolution, read in the tube.** The cell `G` is the cross
reglued cell of `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`, whose two
new seams still meet at the centre of the transverse cross.

Each field is one geometric fact:

* `cell`, `domain_eq` : the resolution is a new map on the same source disk, not a
  reparametrisation of `G` and not an ambient postcomposition, either of which would preserve
  every coincidence of values and so could never delete a branch;
* `coord`, `bijOn_coord` : the part of the source disk lying over the parametrised cylinder is
  two strips, identified with the two model strips `bentSource`;
* `reglued_eq` : over the parametrised cylinder the reglued map is the model raw cross reglue
  `crossSeamInclude`, that is, each strip is sent to its bent transverse sheet;
* `resolved_eq` : over the parametrised cylinder the resolved map is the model chord resolution
  `crossSeamResolve`, that is, each strip is sent to its chord sheet;
* `eqOn_compl` : away from the parametrised cylinder the resolution changes nothing;
* `normal` : the resolved cell is again a normal singular cell over the same boundary data.

The source is split along the closed set `T.chart '' spliceCylinder` and not along the open
`U`. With `U` the first three fields compute `⇑G '' G.domain ∩ U`, which is relatively open in
the connected image of the source disk, as the compact set `T.chart '' bentFigure`, and so
force the whole reglued cell into one tube; with the parametrised cylinder both sides are
compact. The two facts that carry the conclusions back to the open `U`, which
`CrossSeamResolutionData` still uses, are `CrossSeamTubeData.image_subset_tube` and
`CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder`. -/
structure CrossSeamRegluedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) (G : SingularTwoCell M) where
  /-- The resolved singular two cell. -/
  cell : SingularTwoCell M
  /-- The resolution keeps the source disk of the reglued cell. -/
  domain_eq : cell.domain = G.domain
  /-- The model coordinate on the part of the source disk lying over the parametrised
  cylinder. -/
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  /-- The part of the source disk lying over the parametrised cylinder is carried bijectively
  onto the two model strips of the raw cross reglue. -/
  bijOn_coord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource
  /-- Over the parametrised cylinder the reglued map is the model raw cross reglue. -/
  reglued_eq : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  /-- Over the parametrised cylinder the resolved map is the model chord resolution. -/
  resolved_eq : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  /-- Away from the parametrised cylinder the resolution changes nothing. -/
  eqOn_compl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  /-- The resolved cell is again a normal singular cell over the same boundary data. -/
  normal : NormalSingularCellData cell BdM B

namespace CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

/-- Over the parametrised cylinder the resolved cell covers exactly the parametrised
replacement figure. -/
theorem image_cell_tube (R : CrossSeamRegluedData T G) :
    R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = T.chart '' spliceFigure := by
  have h : R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = (T.chart ∘ crossSeamResolve ∘ R.coord) ''
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    Set.image_congr fun x hx => R.resolved_eq hx
  rw [h, Set.image_comp, Set.image_comp, R.bijOn_coord.image_eq, image_crossSeamResolve]

/-- The resolution keeps the part of the source disk lying over the parametrised cylinder
inside it: the chords of the cross section square never leave the cross section. -/
theorem mapsTo_cell_tube (R : CrossSeamRegluedData T G) :
    MapsTo R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      (T.chart '' spliceCylinder) := by
  intro x hx
  have h : R.cell x ∈ R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := ⟨x, hx, rfl⟩
  rw [R.image_cell_tube] at h
  exact Set.image_mono spliceFigure_subset_spliceCylinder h

/-- **The resolution is injective over the parametrised cylinder.** This is the model theorem
`injOn_crossSeamResolve`, that the two chord sheets are disjoint, read through the tube. -/
theorem injOn_cell_tube (R : CrossSeamRegluedData T G) :
    InjOn R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
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

/-- **The resolved cell has no double point inside the parametrised cylinder.** This is the
exact model statement `doublePointSet_crossSeamResolve` read through the tube. -/
theorem doublePointSet_cell_tube (R : CrossSeamRegluedData T G) :
    doublePointSet R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr R.injOn_cell_tube

/-- **The raw cross reglue still has the whole branch as its double point set inside the
parametrised cylinder.** This is the model statement `doublePointSet_crossSeamInclude` read
through the tube, and it is the defect
`hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain` of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` in local form. -/
theorem doublePointSet_reglued_tube (R : CrossSeamRegluedData T G) :
    doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) =
      hD.singularSet.branchCarrier c := by
  have hinj : InjOn T.chart (crossSeamInclude '' bentSource) := by
    rw [image_crossSeamInclude]
    exact T.isTube.injOn_chart.mono bentFigure_subset_spliceCylinder
  have hcongr : doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = doublePointSet ((T.chart ∘ crossSeamInclude) ∘ R.coord)
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    doublePointSet_congr R.reglued_eq
  rw [hcongr, doublePointSet_comp_of_bijOn R.bijOn_coord,
    image_doublePointSet_of_injOn hinj, doublePointSet_crossSeamInclude,
    T.isTube.image_spliceCore]

/-- Away from the parametrised cylinder the resolved cell takes its values outside it. -/
theorem cell_notMem_tube (R : CrossSeamRegluedData T G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :
    R.cell x ∉ T.chart '' spliceCylinder := by
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
cross reglue itself changes no double point outside the parametrised cylinder; it is a property
of `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` and not of the seam
resolution, and it is not proved here. -/
theorem doublePointSet_cell_eq (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
    doublePointSet R.cell R.cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  rw [T.doublePointSet_sdiff_image_spliceCylinder, ← hGD, R.domain_eq]
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
    rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW <;>
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hz with hzV | hzW
    · exact absurd (R.injOn_cell_tube hxV hzV (hyx.trans hyz.symm)) hxz
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.mapsTo_cell_tube hxV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.cell_notMem_tube hzW
      exact h2 h1
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.mapsTo_cell_tube hzV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.cell_notMem_tube hxW
      exact h2 h1
    · refine ⟨⟨x, hx, z, hz, hxz, ?_, ?_⟩, ?_⟩
      · rw [← R.eqOn_compl hxW]; exact hyx
      · rw [← R.eqOn_compl hzW]; exact hyz
      · rw [← hyx]; exact R.cell_notMem_tube hxW
  · rintro y ⟨⟨x, hx, z, hz, hxz, hyx, hyz⟩, hyU⟩
    have hxU : G x ∉ T.chart '' spliceCylinder := by rw [hyx]; exact hyU
    have hzU : G z ∉ T.chart '' spliceCylinder := by rw [hyz]; exact hyU
    exact ⟨x, hx, z, hz, hxz, (R.eqOn_compl ⟨hx, hxU⟩).trans hyx,
      (R.eqOn_compl ⟨hz, hzU⟩).trans hyz⟩

/-- **The resolved image stays inside the old image together with the tube.** The resolved map is
not a reparametrisation of the reglued map, so its image is in general not contained in the old
image; the excess is confined to the parametrised cylinder, hence to the tube. -/
theorem image_cell_subset (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain) :
    R.cell '' R.cell.domain ⊆ D '' D.domain ∪ U := by
  rw [R.domain_eq]
  rintro _ ⟨x, hx, rfl⟩
  rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
  · exact Or.inr (T.isTube.image_subset_tube (R.mapsTo_cell_tube hxV))
  · exact Or.inl (hGim ⟨x, hx, (R.eqOn_compl hxW).symm⟩)

/-- **The replacement is glued in along the same curves.** On the lateral boundary of the tube
the resolved image and the old image agree, because the two bent arcs and the two chords have the
same lateral trace. -/
theorem image_cell_inter_lateral (R : CrossSeamRegluedData T G) :
    R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) =
      D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
  have hlat : T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) ⊆ T.chart '' spliceCylinder :=
    Set.image_mono spliceSquareBoundary_prod_subset_spliceCylinder
  have hleft : R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = T.chart '' spliceFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
      rw [R.domain_eq] at hx
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
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
    rw [T.isTube.image_crossingFigure, Set.inter_assoc, Set.inter_eq_right.mpr hlat]
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
the cross reglue changes no double point outside the parametrised cylinder.

The two remaining fields of `CrossSeamResolutionData`, the branch correspondence and its
compatibility with branch carriers, are supplied separately in
`crossSeamResolutionDataOfTube`. -/
theorem exists_resolved_cell_of_tube (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
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
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
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
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
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
the base interval, onto the part of the surface lying in the parametrised cylinder, and whose
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
