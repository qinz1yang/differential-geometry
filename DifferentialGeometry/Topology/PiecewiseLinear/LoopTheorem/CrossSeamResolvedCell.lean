/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap

/-!
# The resolved cell of a cross seam tube is constructed, not assumed

`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube` records the cross
reglued cell in the normal form of a tube as `CrossSeamRegluedData`, but that structure carries
the resolved cell as a *field*: the piecewise linearity, indeed the very existence, of the
replacement map is assumed. Moreover its `bijOn_coord` only asks for a set theoretic bijection
between the part of the source disk lying over the tube and the two model strips, which is
compatible with a discontinuous reassignment of the two sheet labels.

This file removes both defects. It isolates a piecewise linear reading of the cross reglue and
*builds* the resolved cell from it by a finite piecewise linear gluing.

## The two hypotheses

`PLSeamTubeChart M chart` is the piecewise linear content of the tube parametrisation, and
nothing else: a `PLPieceIn` for `chart '' spliceCylinder` whose simplicial complex fills the
model cylinder and whose map is `chart` itself. Its only use is
`PLSeamTubeChart.isPLOn_comp`, which says that postcomposing a piecewise affine map of a plane
polyhedron into the model cylinder with `chart` gives a map that is piecewise linear as a map
into the manifold. That is exactly `PLPieceIn.isPLOn_comp`, and it is the reason for choosing
this form of the hypothesis: the chart of the manifold appears only through the
`isPiecewiseAffineOn_chart` field of the piece, so no separate compatibility between `chart` and
the atlas of `M` has to be assumed. The side, boundary and buffer clauses of a full boundary
tube are deliberately *not* included here; they belong to the producer of the tube.

`PLCrossSeamReading chart G` is the piecewise linear reading of the cross reglue `G`. Its
content is Moise's decomposition of the source disk:

* `sourcePos`, `sourceNeg` are the two source pieces of the part of the disk lying over the
  parametrised cylinder, and `isPLHomeomorphOn_pos`, `isPLHomeomorphOn_neg` say that the
  *untagged* coordinate `fun x => (coord x).2` is a piecewise linear homeomorphism from each of
  them onto the corresponding bent sheet. This is the clause that a merely set theoretic
  `coord` cannot supply.
* `coord_fst_pos`, `coord_fst_neg` fix the sheet label on each piece. Being constant on each
  piece, the label cannot jump; the disjointness of the two pieces is then a *theorem*,
  `PLCrossSeamReading.disjoint_source`, and not a further hypothesis.
* `face` is the closure of the rest of the disk, a polyhedron, and `union_eq` says that the
  three pieces cover the disk.
* `overlap_lateral` is the lateral stationarity clause: where a source piece meets the face the
  model coordinate lies on the lateral attaching wall of the cylinder.
* `boundary_iff_end` says that over the parametrised cylinder the boundary of the source disk
  is exactly what lies over the two end cross sections of the tube.

**No field asserts that a resolved cell exists, or that it is piecewise linear.**

## The construction

`PLCrossSeamReading.resolvedCell` is the map of equation (7) of the reading: on the two source
pieces it is `chart ∘ crossSeamResolve ∘ coord`, elsewhere it is `G`. It is piecewise linear by
two applications of `IsPLOn.piecewise_of_isClosed` over the closed polyhedral cover
`{sourcePos, sourceNeg, face}`: on each source piece it is a composite of piecewise affine maps
followed by `chart`, on the face it is `G`, and on the overlap the two agree by
`overlap_lateral` together with the lateral stationarity of the model,
`crossSeamResolvePos_eqOn_lateral` and `crossSeamResolveNeg_eqOn_lateral`.

`PLCrossSeamReading.toCrossSeamRegluedData` then produces a full `CrossSeamRegluedData`, so
every consumer proved in `CrossSeamTube` applies unchanged. Two further facts are proved here
because they need no gluing theory: `image_resolvedCell_subset`, the image control, and
`mapsTo_resolvedCell_frontier`, which says that over the tube the boundary curve of the
resolved cell moves inside the two end cross sections only.

## Non-degeneracy

The reading cannot be satisfied degenerately, and this is proved here rather than checked on
one witness.

* `sourcePos_nonempty` and `sourceNeg_nonempty`: the coordinate is onto the two model strips,
  so the case `sourcePos ∪ sourceNeg = ∅`, the tube missed by `G`, is *not* a case of this
  structure. It is not a case of `CrossSeamRegluedData` either, whose `bijOn_coord` already
  forbids it, so nothing is lost.
* `source_ssubset_domain` and `face_nonempty`: a piecewise linear ball is connected while the
  two source pieces are disjoint and closed, so the case `face = ∅` is impossible as well, and
  the source disk is strictly larger than the part lying over the tube.
* `disjoint_source`: the two source pieces cannot share even a frontier point, because the
  sheet label is constant on each of them.
* `corner_of_mem_face`: at the four points where the lateral wall meets an end cross section
  the lateral clause and the boundary clause are both in force and say compatible things.

`nonempty_plSeamTubeChart_spliceEmbedding` inhabits `PLSeamTubeChart` at the model
parametrisation `spliceEmbedding`, which `crossSeamTubeCore_spliceEmbedding` already shows
satisfies the geometric tube contract in a non-degenerate configuration.

An inhabitant of `PLCrossSeamReading` itself is *not* given here, and none of the statements
above claims one. By the four facts listed above any such inhabitant is necessarily the
non-degenerate configuration: a single source disk carrying two disjoint sub-disks that run
through the tube on the two bent sheets, joined through a nonempty complementary face whose
image leaves the parametrised cylinder between the four lateral walls. Producing it means
writing out an explicit model cell: a rectangle `Icc 0 5 ×ˢ Icc 0 1` of the source plane with
`sourcePos = Icc 1 2 ×ˢ Icc 0 1`, `sourceNeg = Icc 3 4 ×ˢ Icc 0 1`, the two bent arc
parametrisations `a ↦ (max (3 - 2 * a) 0, min (3 - 2 * a) 0)` and
`a ↦ (min (2 * a - 7) 0, max (2 * a - 7) 0)` on them, and a complementary face whose image
leaves the cross section square, which takes eight affine pieces in all: one out of each free
end and two for the connector between the two sheets, since the straight segment between two
lateral wall points of the square runs back through the square. That construction is left to
the producer lane; nothing above depends on it.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-! ### Selecting a sheet of the model resolution -/

/-- On the first source strip the tagged model resolution is the first fiberwise resolution. -/
theorem crossSeamResolve_eq_pos {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q.1 = true) :
    crossSeamResolve q = crossSeamResolvePos q.2 := by
  have h : q = (true, q.2) := Prod.ext hq rfl
  rw [h, crossSeamResolve_true]

/-- On the second source strip the tagged model resolution is the second fiberwise
resolution. -/
theorem crossSeamResolve_eq_neg {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q.1 = false) :
    crossSeamResolve q = crossSeamResolveNeg q.2 := by
  have h : q = (false, q.2) := Prod.ext hq rfl
  rw [h, crossSeamResolve_false]

/-- The first bent sheet of the raw cross reglue is nonempty. -/
theorem bentSheetPos_nonempty : bentSheetPos.Nonempty :=
  ⟨(((1 : ℝ), (0 : ℝ)), (0 : ℝ)), mem_bentArcPos.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩),
    ⟨le_rfl, zero_le_one⟩⟩

/-- The second bent sheet of the raw cross reglue is nonempty. -/
theorem bentSheetNeg_nonempty : bentSheetNeg.Nonempty :=
  ⟨((((-1) : ℝ), (0 : ℝ)), (0 : ℝ)), mem_bentArcNeg.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
    ⟨le_rfl, zero_le_one⟩⟩

/-! ### The piecewise linear content of the tube parametrisation -/

/-- **The tube parametrisation, read piecewise linearly.** The model cylinder is filled by a
finite simplicial complex, and the parametrisation is the map of a `PLPieceIn` on it. This is
the weakest hypothesis under which `PLPieceIn.isPLOn_comp` applies, and it is the only piece of
the full boundary tube contract that the construction of the resolved cell needs: the side
clause `chart '' spliceCylinder ⊆ W`, the boundary clause and the buffer clause around the
selected branch are not used here and are not assumed. -/
structure PLSeamTubeChart (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (chart : (ℝ × ℝ) × ℝ → M) where
  /-- The parametrised cylinder as a piecewise linear piece of the manifold. -/
  piece : PLPieceIn ((ℝ × ℝ) × ℝ) 3 M (chart '' spliceCylinder)
  /-- The simplicial complex of the piece fills the model cylinder. -/
  space_eq : piece.complex.space = spliceCylinder
  /-- The map of the piece is the tube parametrisation. -/
  map_eq : piece.map = chart

namespace PLSeamTubeChart

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M}

/-- **Composing with the tube parametrisation preserves piecewise linearity.** A piecewise
affine map of a set of the source plane into the model cylinder becomes, after the tube
parametrisation, a piecewise linear map into the manifold. This is the only consequence of
`PLSeamTubeChart` that the construction below uses. -/
theorem isPLOn_comp (C : PLSeamTubeChart M chart)
    {f : EuclideanSpace ℝ (Fin 2) → (ℝ × ℝ) × ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hf : IsPiecewiseAffineOn f P) (hmap : MapsTo f P spliceCylinder) :
    IsPLOn 2 3 (chart ∘ f) P := by
  have hmap' : MapsTo f P C.piece.complex.space := by
    rw [C.space_eq]
    exact hmap
  have h := C.piece.isPLOn_comp hf hmap'
  rwa [C.map_eq] at h

end PLSeamTubeChart

/-! ### The piecewise linear reading of the cross reglue -/

/-- **A piecewise linear reading of the boundary cross reglue.** The source disk of the cross
reglued cell `G` is decomposed into two compact polyhedral pieces `sourcePos`, `sourceNeg`
lying over the parametrised cylinder and a complementary polyhedral `face`, together with a
tagged model coordinate `coord` which restricts to a piecewise linear homeomorphism of each
piece onto the corresponding bent sheet of the model.

The two defects of `CrossSeamRegluedData` that this repairs are that the resolved cell is there
a field rather than a construction, and that `bijOn_coord` there is a bare set theoretic
bijection, which cannot exclude a discontinuous reassignment of the two sheet labels. Here the
labels are constant on the two pieces and the untagged coordinate is a piecewise linear
homeomorphism on each of them.

No field asserts that a resolved cell exists or that it is piecewise linear; that is the
content of `PLCrossSeamReading.resolvedCell`. -/
structure PLCrossSeamReading {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (chart : (ℝ × ℝ) × ℝ → M)
    (G : SingularTwoCell M) where
  /-- The tagged model coordinate on the part of the source disk lying over the cylinder. -/
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  /-- The source piece carrying the first bent sheet. -/
  sourcePos : Set (EuclideanSpace ℝ (Fin 2))
  /-- The source piece carrying the second bent sheet. -/
  sourceNeg : Set (EuclideanSpace ℝ (Fin 2))
  /-- The closure of the part of the source disk not lying over the cylinder. -/
  face : Set (EuclideanSpace ℝ (Fin 2))
  /-- Forgetting the sheet label, the coordinate is a piecewise linear homeomorphism of the
  first source piece onto the first bent sheet. -/
  isPLHomeomorphOn_pos : IsPLHomeomorphOn (fun x => (coord x).2) sourcePos bentSheetPos
  /-- Forgetting the sheet label, the coordinate is a piecewise linear homeomorphism of the
  second source piece onto the second bent sheet. -/
  isPLHomeomorphOn_neg : IsPLHomeomorphOn (fun x => (coord x).2) sourceNeg bentSheetNeg
  /-- The sheet label is constantly the first one on the first source piece. -/
  coord_fst_pos : ∀ x ∈ sourcePos, (coord x).1 = true
  /-- The sheet label is constantly the second one on the second source piece. -/
  coord_fst_neg : ∀ x ∈ sourceNeg, (coord x).1 = false
  /-- The two source pieces are exactly the part of the source disk lying over the parametrised
  cylinder. -/
  source_eq : sourcePos ∪ sourceNeg = G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder)
  /-- The complementary face is a polyhedron. -/
  isPolyhedron_face : IsPolyhedron face
  /-- The three pieces cover the source disk. -/
  union_eq : sourcePos ∪ sourceNeg ∪ face = G.domain
  /-- Over the parametrised cylinder the reglued map is the model raw cross reglue. -/
  reglued_eq : EqOn (⇑G) (chart ∘ crossSeamInclude ∘ coord) (sourcePos ∪ sourceNeg)
  /-- Where a source piece meets the complementary face, the model coordinate lies on the
  lateral attaching wall of the cylinder. -/
  overlap_lateral : ∀ x ∈ (sourcePos ∪ sourceNeg) ∩ face,
    (coord x).2 ∈ spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1
  /-- Over the parametrised cylinder, the boundary of the source disk is exactly what lies over
  the two ends of the base interval. -/
  boundary_iff_end : ∀ x ∈ sourcePos ∪ sourceNeg,
    (x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)

namespace PLCrossSeamReading

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}

/-- The part of the source disk lying over the parametrised cylinder: the union of the two
source pieces. It is named rather than written out because the resolved map is defined by a
case split on it, and an opaque name keeps that case split compatible with the gluing lemma. -/
def tubeSource (R : PLCrossSeamReading chart G) : Set (EuclideanSpace ℝ (Fin 2)) :=
  R.sourcePos ∪ R.sourceNeg

/-- Membership over the parametrised cylinder means membership in one of the two pieces. -/
theorem mem_tubeSource (R : PLCrossSeamReading chart G) {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ R.tubeSource ↔ x ∈ R.sourcePos ∨ x ∈ R.sourceNeg := Iff.rfl

/-- The two source pieces are exactly the part of the source disk lying over the parametrised
cylinder. -/
theorem tubeSource_eq (R : PLCrossSeamReading chart G) :
    R.tubeSource = G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder) := R.source_eq

/-- The part over the cylinder and the complementary face cover the source disk. -/
theorem tubeSource_union_face (R : PLCrossSeamReading chart G) :
    R.tubeSource ∪ R.face = G.domain := R.union_eq

/-- **The two source pieces are disjoint.** This is not an extra hypothesis: a point of both
would carry both sheet labels. -/
theorem disjoint_source (R : PLCrossSeamReading chart G) :
    Disjoint R.sourcePos R.sourceNeg := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact Bool.noConfusion ((R.coord_fst_pos x hx).symm.trans (R.coord_fst_neg x hx'))

/-- The tagged coordinate carries the two source pieces bijectively onto the two model strips.
This is the `bijOn_coord` field of `CrossSeamRegluedData`, here a consequence of the two
piecewise linear homeomorphisms and the constancy of the sheet labels. -/
theorem bijOn_coord (R : PLCrossSeamReading chart G) :
    BijOn R.coord R.tubeSource bentSource := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases R.mem_tubeSource.mp hx with hx | hx
    · exact mem_bentSource.mpr
        (Or.inl ⟨R.coord_fst_pos x hx, R.isPLHomeomorphOn_pos.bijOn.mapsTo hx⟩)
    · exact mem_bentSource.mpr
        (Or.inr ⟨R.coord_fst_neg x hx, R.isPLHomeomorphOn_neg.bijOn.mapsTo hx⟩)
  · intro x hx z hz hxz
    rcases R.mem_tubeSource.mp hx with hx | hx <;>
      rcases R.mem_tubeSource.mp hz with hz | hz
    · exact R.isPLHomeomorphOn_pos.bijOn.injOn hx hz (congrArg Prod.snd hxz)
    · exact absurd (congrArg Prod.fst hxz) (by
        rw [R.coord_fst_pos x hx, R.coord_fst_neg z hz]; simp)
    · exact absurd (congrArg Prod.fst hxz) (by
        rw [R.coord_fst_neg x hx, R.coord_fst_pos z hz]; simp)
    · exact R.isPLHomeomorphOn_neg.bijOn.injOn hx hz (congrArg Prod.snd hxz)
  · intro q hq
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · obtain ⟨x, hx, hcx⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn hs
      exact ⟨x, R.mem_tubeSource.mpr (Or.inl hx),
        Prod.ext ((R.coord_fst_pos x hx).trans hb.symm) hcx⟩
    · obtain ⟨x, hx, hcx⟩ := R.isPLHomeomorphOn_neg.bijOn.surjOn hs
      exact ⟨x, R.mem_tubeSource.mpr (Or.inr hx),
        Prod.ext ((R.coord_fst_neg x hx).trans hb.symm) hcx⟩

/-- The first source piece is a polyhedron, being a piecewise linear image of the first bent
sheet. -/
theorem isPolyhedron_sourcePos (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.sourcePos := by
  have h := R.isPLHomeomorphOn_pos.symm
  rw [← h.image_eq]
  exact isPLBall_bentSheetPos.isPolyhedron.image_of_isPiecewiseAffineOn h.isPiecewiseAffineOn
    h.bijOn.injOn

/-- The second source piece is a polyhedron. -/
theorem isPolyhedron_sourceNeg (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.sourceNeg := by
  have h := R.isPLHomeomorphOn_neg.symm
  rw [← h.image_eq]
  exact isPLBall_bentSheetNeg.isPolyhedron.image_of_isPiecewiseAffineOn h.isPiecewiseAffineOn
    h.bijOn.injOn

/-- The part of the source disk lying over the parametrised cylinder is a polyhedron. -/
theorem isPolyhedron_source (R : PLCrossSeamReading chart G) :
    IsPolyhedron R.tubeSource :=
  R.isPolyhedron_sourcePos.union R.isPolyhedron_sourceNeg

/-- The complementary face lies in the source disk. -/
theorem face_subset_domain (R : PLCrossSeamReading chart G) : R.face ⊆ G.domain := by
  rw [← R.tubeSource_union_face]
  exact subset_union_right

/-- The two source pieces lie in the source disk. -/
theorem source_subset_domain (R : PLCrossSeamReading chart G) :
    R.tubeSource ⊆ G.domain := by
  rw [← R.tubeSource_union_face]
  exact subset_union_left

/-! ### The resolved map is piecewise linear -/

/-- On the first source piece the tagged model resolution is the first fiberwise resolution of
the untagged coordinate. -/
theorem eqOn_resolve_pos (R : PLCrossSeamReading chart G) :
    EqOn (crossSeamResolve ∘ R.coord) (crossSeamResolvePos ∘ fun x => (R.coord x).2)
      R.sourcePos := fun x hx => crossSeamResolve_eq_pos (R.coord_fst_pos x hx)

/-- On the second source piece the tagged model resolution is the second fiberwise
resolution. -/
theorem eqOn_resolve_neg (R : PLCrossSeamReading chart G) :
    EqOn (crossSeamResolve ∘ R.coord) (crossSeamResolveNeg ∘ fun x => (R.coord x).2)
      R.sourceNeg := fun x hx => crossSeamResolve_eq_neg (R.coord_fst_neg x hx)

/-- The model resolution of the coordinate is piecewise affine on the first source piece. -/
theorem isPiecewiseAffineOn_resolve_pos (R : PLCrossSeamReading chart G) :
    IsPiecewiseAffineOn (crossSeamResolve ∘ R.coord) R.sourcePos := by
  have h := (isPLHomeomorphOn_crossSeamResolvePos.isPiecewiseAffineOn.comp
    R.isPLHomeomorphOn_pos.isPiecewiseAffineOn).mono_of_isPolyhedron R.isPolyhedron_sourcePos
    fun x hx => ⟨hx, R.isPLHomeomorphOn_pos.bijOn.mapsTo hx⟩
  exact h.congr R.eqOn_resolve_pos

/-- The model resolution of the coordinate is piecewise affine on the second source piece. -/
theorem isPiecewiseAffineOn_resolve_neg (R : PLCrossSeamReading chart G) :
    IsPiecewiseAffineOn (crossSeamResolve ∘ R.coord) R.sourceNeg := by
  have h := (isPLHomeomorphOn_crossSeamResolveNeg.isPiecewiseAffineOn.comp
    R.isPLHomeomorphOn_neg.isPiecewiseAffineOn).mono_of_isPolyhedron R.isPolyhedron_sourceNeg
    fun x hx => ⟨hx, R.isPLHomeomorphOn_neg.bijOn.mapsTo hx⟩
  exact h.congr R.eqOn_resolve_neg

/-- The resolution keeps the two source pieces over the model cylinder: the chords of the cross
section square never leave the cross section. -/
theorem mapsTo_resolve (R : PLCrossSeamReading chart G) :
    MapsTo (crossSeamResolve ∘ R.coord) R.tubeSource spliceCylinder := by
  intro x hx
  refine spliceFigure_subset_spliceCylinder ?_
  rw [← image_crossSeamResolve]
  exact ⟨R.coord x, R.bijOn_coord.mapsTo hx, rfl⟩

/-- **The resolved map is piecewise linear over the tube.** On each source piece it is a
composite of piecewise affine maps into the model cylinder followed by the tube
parametrisation, and the two pieces are closed polyhedra. -/
theorem isPLOn_resolve (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.tubeSource := by
  classical
  have hpos : IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.sourcePos :=
    C.isPLOn_comp R.isPiecewiseAffineOn_resolve_pos fun x hx =>
      R.mapsTo_resolve (R.mem_tubeSource.mpr (Or.inl hx))
  have hneg : IsPLOn 2 3 (chart ∘ crossSeamResolve ∘ R.coord) R.sourceNeg :=
    C.isPLOn_comp R.isPiecewiseAffineOn_resolve_neg fun x hx =>
      R.mapsTo_resolve (R.mem_tubeSource.mpr (Or.inr hx))
  have h := hpos.piecewise_of_isClosed hneg R.isPolyhedron_sourcePos.isClosed
    R.isPolyhedron_sourceNeg.isClosed fun _ _ => rfl
  rwa [Set.piecewise_same] at h

/-- **The replacement is glued in along the lateral wall.** Where a source piece meets the
complementary face the resolved map agrees with the reglued map, because there the model
coordinate lies on the lateral attaching wall and the model resolution is stationary on it. -/
theorem eqOn_overlap (R : PLCrossSeamReading chart G) :
    EqOn (chart ∘ crossSeamResolve ∘ R.coord) (⇑G)
      (R.tubeSource ∩ R.face) := by
  intro x hx
  have hlat := R.overlap_lateral x hx
  have hq : R.coord x ∈ bentSource := R.bijOn_coord.mapsTo hx.1
  have hfix : crossSeamResolve (R.coord x) = (R.coord x).2 := by
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · rw [crossSeamResolve_eq_pos hb]
      exact crossSeamResolvePos_eqOn_lateral ⟨hs, hlat⟩
    · rw [crossSeamResolve_eq_neg hb]
      exact crossSeamResolveNeg_eqOn_lateral ⟨hs, hlat⟩
  change chart (crossSeamResolve (R.coord x)) = G x
  rw [hfix, R.reglued_eq hx.1]
  rfl

/-! ### The resolved cell -/

open Classical in
/-- **The resolved cell, constructed.** On the two source pieces it is the tube parametrisation
of the model chord resolution of the coordinate, and on the complementary face it is the cross
reglued map itself. Piecewise linearity is a finite gluing over the closed polyhedral cover
`{sourcePos, sourceNeg, face}` of the source disk. -/
noncomputable def resolvedCell (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    SingularTwoCell M where
  domain := G.domain
  isPLBall_domain := G.isPLBall_domain
  toFun := R.tubeSource.piecewise (chart ∘ crossSeamResolve ∘ R.coord) ⇑G
  isPLOn := by
    have h := (R.isPLOn_resolve C).piecewise_of_isClosed
      (G.isPLOn.mono_of_isPolyhedron R.isPolyhedron_face R.face_subset_domain)
      R.isPolyhedron_source.isClosed R.isPolyhedron_face.isClosed R.eqOn_overlap
    rw [R.tubeSource_union_face] at h
    exact h

/-- The resolution keeps the source disk of the reglued cell. -/
@[simp]
theorem resolvedCell_domain (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    (R.resolvedCell C).domain = G.domain := rfl

open Classical in
/-- Over the parametrised cylinder the resolved cell is the model chord resolution. -/
theorem resolvedCell_apply_of_mem (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ R.tubeSource) :
    R.resolvedCell C x = chart (crossSeamResolve (R.coord x)) :=
  Set.piecewise_eq_of_mem _ _ _ hx

open Classical in
/-- Away from the parametrised cylinder the resolved cell is the reglued cell. -/
theorem resolvedCell_apply_of_notMem (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∉ R.tubeSource) : R.resolvedCell C x = G x :=
  Set.piecewise_eq_of_notMem _ _ _ hx

/-- **The image control of the resolution.** The resolved cell is not a reparametrisation of
the reglued cell, so its image is in general not contained in the old image; the excess is
confined to the parametrised cylinder. This is equation (8) of the reading, in the form that
needs no hypothesis on the tube. -/
theorem image_resolvedCell_subset (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    R.resolvedCell C '' (R.resolvedCell C).domain ⊆
      ⇑G '' G.domain ∪ chart '' spliceCylinder := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxs : x ∈ R.tubeSource
  · refine Or.inr ⟨crossSeamResolve (R.coord x), R.mapsTo_resolve hxs, ?_⟩
    exact (R.resolvedCell_apply_of_mem C hxs).symm
  · exact Or.inl ⟨x, hx, (R.resolvedCell_apply_of_notMem C hxs).symm⟩

/-- **At the two ends of the tube the boundary curve moves inside the end cross sections
only.** This is the consequence of `boundary_iff_end` that the boundary bookkeeping of the
reglue consumes; it uses no closure or cut and paste theory. -/
theorem mapsTo_resolvedCell_frontier (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    MapsTo (R.resolvedCell C) (R.tubeSource ∩ frontier G.domain)
      (chart '' spliceEndDisks) := by
  rintro x ⟨hxs, hxf⟩
  refine ⟨crossSeamResolve (R.coord x), ?_, (R.resolvedCell_apply_of_mem C hxs).symm⟩
  exact crossSeamResolve_mem_spliceEndDisks (R.bijOn_coord.mapsTo hxs)
    ((R.boundary_iff_end x hxs).mp hxf)

/-! ### The reading produces the reglued data of the tube -/

variable {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

open Classical in
/-- **The resolved cell of a tube, constructed from the piecewise linear reading.** Every field
of `CrossSeamRegluedData` mentions the tube only through its parametrisation `T.chart`, so the
reading above, taken at that parametrisation, produces the reglued data outright: the resolved
cell is no longer assumed. All the consumers proved in
`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube` therefore apply
unchanged. -/
noncomputable def toCrossSeamRegluedData (T : CrossSeamTubeData hD c U)
    (R : PLCrossSeamReading T.chart G) (C : PLSeamTubeChart M T.chart) :
    CrossSeamRegluedData T G where
  cell := R.resolvedCell C
  domain_eq := rfl
  coord := R.coord
  bijOn_coord := R.tubeSource_eq ▸ R.bijOn_coord
  reglued_eq := R.tubeSource_eq ▸ R.reglued_eq
  resolved_eq := by
    rw [← R.tubeSource_eq]
    intro x hx
    exact R.resolvedCell_apply_of_mem C hx
  eqOn_compl := by
    intro x hx
    refine R.resolvedCell_apply_of_notMem C fun hxs => ?_
    rw [R.tubeSource_eq] at hxs
    exact hx.2 hxs.2

/-! ### The reading is never degenerate -/

/-- **The first source piece is nonempty.** The coordinate is onto the two model strips, so the
tube cannot be missed by the reglued cell. In particular the degenerate case
`sourcePos ∪ sourceNeg = ∅` is not a case of this structure, exactly as the `bijOn_coord` field
of `CrossSeamRegluedData` already forbids it. -/
theorem sourcePos_nonempty (R : PLCrossSeamReading chart G) : R.sourcePos.Nonempty := by
  obtain ⟨y, hy⟩ := bentSheetPos_nonempty
  obtain ⟨x, hx, -⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn hy
  exact ⟨x, hx⟩

/-- **The second source piece is nonempty.** -/
theorem sourceNeg_nonempty (R : PLCrossSeamReading chart G) : R.sourceNeg.Nonempty := by
  obtain ⟨y, hy⟩ := bentSheetNeg_nonempty
  obtain ⟨x, hx, -⟩ := R.isPLHomeomorphOn_neg.bijOn.surjOn hy
  exact ⟨x, hx⟩

/-- **The part of the source disk lying over the tube is a proper part of it.** The two source
pieces are nonempty, disjoint and closed, while the source disk is a piecewise linear ball,
hence connected. -/
theorem source_ssubset_domain (R : PLCrossSeamReading chart G) :
    R.tubeSource ⊂ G.domain := by
  refine ⟨R.source_subset_domain, fun hsub => ?_⟩
  have hdom : G.domain = R.tubeSource :=
    Subset.antisymm hsub R.source_subset_domain
  obtain ⟨x, hx⟩ := R.sourcePos_nonempty
  obtain ⟨z, hz⟩ := R.sourceNeg_nonempty
  have hconn := G.isPLBall_domain.isConnected.isPreconnected
  obtain ⟨y, hy, hy1, hy2⟩ := hconn R.sourceNegᶜ R.sourcePosᶜ
    R.isPolyhedron_sourceNeg.isClosed.isOpen_compl
    R.isPolyhedron_sourcePos.isClosed.isOpen_compl
    (fun w hw => by
      rcases R.mem_tubeSource.mp (hdom ▸ hw) with hw' | hw'
      · exact Or.inl (Set.disjoint_left.mp R.disjoint_source hw')
      · exact Or.inr fun hw'' => Set.disjoint_left.mp R.disjoint_source hw'' hw')
    ⟨x, R.source_subset_domain (R.mem_tubeSource.mpr (Or.inl hx)),
      Set.disjoint_left.mp R.disjoint_source hx⟩
    ⟨z, R.source_subset_domain (R.mem_tubeSource.mpr (Or.inr hz)), fun hz' =>
      Set.disjoint_left.mp R.disjoint_source hz' hz⟩
  rcases R.mem_tubeSource.mp (hdom ▸ hy) with hy' | hy'
  · exact hy2 hy'
  · exact hy1 hy'

/-- **The complementary face is nonempty.** So the case `face = ∅` is impossible: the two
source pieces alone cannot fill a connected source disk. -/
theorem face_nonempty (R : PLCrossSeamReading chart G) : R.face.Nonempty := by
  obtain ⟨y, hy, hys⟩ := (ssubset_iff_of_subset R.source_subset_domain).mp
    R.source_ssubset_domain
  refine ⟨y, ?_⟩
  rw [← R.tubeSource_union_face] at hy
  rcases hy with hy' | hy'
  · exact absurd hy' hys
  · exact hy'

/-- **The four corners of the tube are jointly constrained, not over constrained.** Where a
source piece meets the complementary face over an end of the base interval, both the lateral
clause `overlap_lateral` and the boundary clause `boundary_iff_end` are in force: the point
lies on the boundary of the source disk, and its model coordinate lies on the lateral
attaching wall and in an end cross section at once, that is, on the boundary square of an end
disk. This is the configuration at the four points where the lateral wall meets the two end
disks, and the two clauses say compatible things there. -/
theorem corner_of_mem_face (R : PLCrossSeamReading chart G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ R.tubeSource ∩ R.face) (hend : (R.coord x).2.2 = 0 ∨ (R.coord x).2.2 = 1) :
    x ∈ frontier G.domain ∧ (R.coord x).2 ∈ spliceEndDisks ∧
      (R.coord x).2.1 ∈ spliceSquareBoundary := by
  have hlat := R.overlap_lateral x hx
  refine ⟨(R.boundary_iff_end x hx.1).mpr hend, ⟨hlat.1.1, ?_⟩, hlat.1⟩
  rcases hend with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

end PLCrossSeamReading

/-! ### The model tube parametrisation is a piecewise linear tube chart -/

/-- The linear placement of the model cylinder in the model three space is piecewise affine on
the cylinder. -/
theorem isPiecewiseAffineOn_spliceEmbedding :
    IsPiecewiseAffineOn (⇑spliceEmbedding) spliceCylinder :=
  (isPiecewiseAffineOn_of_affine_of_isHPolytope spliceEmbedding.toLinearMap.toAffineMap
    isHPolytope_spliceCylinder).congr fun _ _ => rfl

/-- The parametrised model cylinder is a polyhedron of the model three space. -/
theorem isPolyhedron_image_spliceEmbedding :
    IsPolyhedron (⇑spliceEmbedding '' spliceCylinder) :=
  isHPolytope_spliceCylinder.isPolyhedron.image_of_isPiecewiseAffineOn
    isPiecewiseAffineOn_spliceEmbedding spliceEmbedding.injective.injOn

/-- The inverse of the linear placement is piecewise affine on the parametrised cylinder. -/
theorem isPiecewiseAffineOn_spliceEmbedding_symm :
    IsPiecewiseAffineOn (⇑spliceEmbedding.symm) (⇑spliceEmbedding '' spliceCylinder) :=
  ((isPiecewiseAffineOn_of_affine spliceEmbedding.symm.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron isPolyhedron_image_spliceEmbedding
      (subset_univ _)).congr fun _ _ => rfl

/-- **The piecewise linear tube chart contract is not vacuous.** The model parametrisation
`spliceEmbedding` of
`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTube`, which already
satisfies the geometric contract `CrossSeamTubeCore` by `crossSeamTubeCore_spliceEmbedding` in a
configuration that is not degenerate, also satisfies the piecewise linear contract: the model
cylinder is a polytope, so it carries a finite simplicial complex, and the placement is the
restriction of a linear homeomorphism, hence piecewise affine in both directions. -/
theorem nonempty_plSeamTubeChart_spliceEmbedding :
    Nonempty (PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding) := by
  obtain ⟨K, hfin, hspace⟩ := isHPolytope_spliceCylinder.isPolyhedron.exists_simplicialComplex
  have hbij : BijOn (⇑spliceEmbedding) K.space (⇑spliceEmbedding '' spliceCylinder) := by
    rw [hspace]
    exact spliceEmbedding.injective.injOn.bijOn_image
  refine ⟨⟨⟨K, hfin, ⇑spliceEmbedding, hbij,
    spliceEmbedding.continuous.continuousOn, ?_, ?_⟩, hspace, rfl⟩⟩
  · intro e he
    have hrefl : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp he
    subst hrefl
    have hset : K.space ∩ ⇑spliceEmbedding ⁻¹'
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).source = spliceCylinder := by
      rw [OpenPartialHomeomorph.refl_source, preimage_univ, inter_univ, hspace]
    rw [hset]
    exact isPiecewiseAffineOn_spliceEmbedding.congr fun _ _ => rfl
  · intro e he
    have hrefl : e = OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3)) :=
      chartedSpaceSelf_atlas.mp he
    subst hrefl
    have hset : (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).target ∩
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 3))).symm ⁻¹'
          (⇑spliceEmbedding '' spliceCylinder) = ⇑spliceEmbedding '' spliceCylinder := by
      rw [OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.refl_symm]
      exact univ_inter _
    rw [hset]
    refine isPiecewiseAffineOn_spliceEmbedding_symm.congr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : spliceEmbedding x ∈ ⇑spliceEmbedding '' spliceCylinder := ⟨x, hx, rfl⟩
    have h1 : Function.invFunOn (⇑spliceEmbedding) K.space (spliceEmbedding x) = x :=
      spliceEmbedding.injective (hbij.invOn_invFunOn.2 hmem)
    change Function.invFunOn (⇑spliceEmbedding) K.space (spliceEmbedding x) =
      spliceEmbedding.symm (spliceEmbedding x)
    rw [h1, spliceEmbedding.symm_apply_apply]

end DifferentialGeometry.Topology.PiecewiseLinear
