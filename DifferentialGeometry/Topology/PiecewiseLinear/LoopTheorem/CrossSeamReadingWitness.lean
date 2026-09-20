/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import DifferentialGeometry.Topology.PiecewiseLinear.Prism

/-!
# A model cross reglue whose seam the construction resolves

`DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell` builds the
resolved cell of a cross seam tube from a `PLCrossSeamReading`, and proves that no reading can
be degenerate: both source pieces and the complementary face are nonempty, and the part lying
over the tube is a proper part of the source disk. This file supplies the missing inhabitant,
so that those constraints are known to be satisfiable together.

## The model

Everything happens in `M = EuclideanSpace ℝ (Fin 3)` with `chart = spliceEmbedding`, the linear
placement of the model cylinder used by `crossSeamTubeCore_spliceEmbedding`. The source plane
is placed by a second linear homeomorphism `seamWitnessPlane : (ℝ × ℝ) ≃L[ℝ]
EuclideanSpace ℝ (Fin 2)`, so that all the sets below can be written as rectangles of `ℝ × ℝ`.

The source disk is `seamSourceRect = Icc 0 5 ×ˢ Icc 0 1`, cut into five bands by the four walls
`a = 1, 2, 3, 4`:

* `seamRectPos = Icc 1 2 ×ˢ Icc 0 1` runs through the tube on the first bent sheet;
* `seamRectNeg = Icc 3 4 ×ˢ Icc 0 1` runs through it on the second;
* `seamFaceRect` is the remaining three bands `Icc 0 1`, `Icc 2 3` and `Icc 4 5`.

The two source pieces sit strictly inside the rectangle in the `a` direction, which is forced:
`boundary_iff_end` says that over the tube the boundary of the source disk is exactly what lies
over `t ∈ {0, 1}`, so the four walls must be interior, and each of them must be attached to a
band of the face.

The cell is `spliceEmbedding ∘ seamModelMap ∘ seamWitnessPlane.symm`, where
`seamModelMap (a, t) = ((seamArcX (a, t), seamArcY (a, t)), t)` is a product along the base
interval over a piecewise affine curve of the cross section square with eight affine pieces,
written in closed form as a sum of ramps `seamRamp c b (a, t) = c * max (a - b) 0`:

* on `Icc 0 1` the curve is `(2 - a, 0)`, running inward to the wall value `(1, 0) = e₁`, and
  strictly outside the cross section square before it;
* on `Icc 1 2` it is the bent arc parametrisation `seamBentPos a = (max (3 - 2a) 0,
  min (3 - 2a) 0)`, which is the `L` shaped arc `[e₁, 0] ∪ [0, -e₂]` traversed once;
* on `Icc 2 3` it is the connector `(0, -1) → (-2, -2) → (-1, 0)`, two affine pieces. One does
  not suffice: the straight segment from `(0, -1)` to `(-1, 0)` runs back through the square.
  The first piece leaves through `y < -1`, the second returns through `x < -1`;
* on `Icc 3 4` it is `seamBentNeg a = (min (2a - 7) 0, max (2a - 7) 0)`, the arc
  `[-e₁, 0] ∪ [0, e₂]`;
* on `Icc 4 5` it is `(0, a - 3)`, running outward from the wall value `(0, 1) = e₂` through
  `y > 1`.

Since every piece is a product with `Icc 0 1` in the base coordinate, and `seamModelMap` never
moves that coordinate, the cylinder condition reduces to the cross section square throughout;
the end faces `t = 0` and `t = 1` of the three face bands lie in the planes `t = 0, 1` but
outside the square, so they do not meet the parametrised cylinder either. That is what makes
`source_eq` an equality: `seamWitnessCell ⁻¹' (spliceEmbedding '' spliceCylinder)` meets the
source disk exactly in `seamRectPos ∪ seamRectNeg`.

## What the witness shows

`seamWitnessReading` is the reading, `nonempty_plCrossSeamReading_seamWitnessCell` its bare
existence statement. It is not degenerate:

* `seamWitnessReading_sourcePos_nonempty`, `seamWitnessReading_sourceNeg_nonempty`,
  `seamWitnessReading_face_nonempty`, `seamWitnessReading_tubeSource_ssubset`, instances of the
  general theorems of `CrossSeamResolvedCell`;
* `seamWitnessCell_notInjOn` and `mem_doublePointSet_seamWitnessCell`: the cell really is a
  touching seam going in. The two bent sheets meet at the centre of the cross section, so
  `(3 / 2, 0)` and `(7 / 2, 0)` are distinct source points with the same image, and that image
  is a double point of the cell *inside the tube part of the source disk*;
* `doublePointSet_resolvedCell_seamWitness`: nothing comes out. Over the very same set
  `seamWitnessReading.tubeSource` the resolved cell has no double point at all.

The last statement is proved from a general theorem, `PLCrossSeamReading.injOn_resolvedCell`,
which needs no tube data: the injectivity of `chart` on the model cylinder is already part of
`PLSeamTubeChart` through the `bijOn` field of its piece, and the model injectivity is
`injOn_crossSeamResolve`.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-! ### The resolved cell is injective over the tube -/

universe u

namespace PLCrossSeamReading

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}

/-- The tube parametrisation is injective on the model cylinder: this is the `bijOn` field of
the piece, read through `space_eq` and `map_eq`. -/
theorem injOn_chart_of_pLSeamTubeChart (C : PLSeamTubeChart M chart) :
    InjOn chart spliceCylinder := by
  have h := C.piece.bijOn.injOn
  rw [C.space_eq, C.map_eq] at h
  exact h

/-- **The resolved cell is injective over the tube.** The coordinate is injective there, the
model chord resolution is injective on the two model strips, and the tube parametrisation is
injective on the model cylinder. No tube data is needed. -/
theorem injOn_resolvedCell (R : PLCrossSeamReading chart G) (C : PLSeamTubeChart M chart) :
    InjOn (R.resolvedCell C) R.tubeSource := by
  intro x hx z hz hxz
  rw [R.resolvedCell_apply_of_mem C hx, R.resolvedCell_apply_of_mem C hz] at hxz
  have hmodel := injOn_chart_of_pLSeamTubeChart C (R.mapsTo_resolve hx) (R.mapsTo_resolve hz) hxz
  exact R.bijOn_coord.injOn hx hz
    (injOn_crossSeamResolve (R.bijOn_coord.mapsTo hx) (R.bijOn_coord.mapsTo hz) hmodel)

/-- **The resolved cell has no double point over the tube.** -/
theorem doublePointSet_resolvedCell (R : PLCrossSeamReading chart G)
    (C : PLSeamTubeChart M chart) :
    doublePointSet (R.resolvedCell C) R.tubeSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr (R.injOn_resolvedCell C)

end PLCrossSeamReading

/-! ### The source plane of the witness -/

/-- A linear placement of the coordinate plane as the source plane of a singular two cell, so
that the source sets of the witness can be written as rectangles of `ℝ × ℝ`. -/
noncomputable def seamWitnessPlane : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- Membership in a placed set of the source plane. -/
theorem mem_image_seamWitnessPlane {S : Set (ℝ × ℝ)} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ ⇑seamWitnessPlane '' S ↔ seamWitnessPlane.symm x ∈ S := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [seamWitnessPlane.symm_apply_apply]
  · intro h
    exact ⟨seamWitnessPlane.symm x, h, seamWitnessPlane.apply_symm_apply x⟩

/-- The placement is piecewise affine on any polyhedron. -/
theorem isPiecewiseAffineOn_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPiecewiseAffineOn (⇑seamWitnessPlane) S :=
  (isPiecewiseAffineOn_of_affine seamWitnessPlane.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)

/-- Placing a polyhedron of the coordinate plane is a piecewise linear homeomorphism. -/
theorem isPLHomeomorphOn_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn (⇑seamWitnessPlane) S (⇑seamWitnessPlane '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS (isPiecewiseAffineOn_seamWitnessPlane hS)
    seamWitnessPlane.injective.injOn.bijOn_image

/-- A placed polyhedron of the source plane is a polyhedron. -/
theorem isPolyhedron_image_seamWitnessPlane {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPolyhedron (⇑seamWitnessPlane '' S) :=
  hS.image_of_isPiecewiseAffineOn (isPiecewiseAffineOn_seamWitnessPlane hS)
    seamWitnessPlane.injective.injOn

/-- The inverse placement carries a placed set back bijectively. -/
theorem bijOn_seamWitnessPlaneSymm (S : Set (ℝ × ℝ)) :
    BijOn (⇑seamWitnessPlane.symm) (⇑seamWitnessPlane '' S) S := by
  refine ⟨fun x hx => mem_image_seamWitnessPlane.mp hx, seamWitnessPlane.symm.injective.injOn,
    fun p hp => ⟨seamWitnessPlane p, ⟨p, hp, rfl⟩, seamWitnessPlane.symm_apply_apply p⟩⟩

/-- The inverse placement is piecewise affine on any polyhedron. -/
theorem isPiecewiseAffineOn_seamWitnessPlaneSymm {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsPolyhedron S) : IsPiecewiseAffineOn (⇑seamWitnessPlane.symm) S :=
  (isPiecewiseAffineOn_of_affine seamWitnessPlane.symm.toLinearMap.toAffineMap
    isOpen_univ).mono_of_isPolyhedron hS (subset_univ _)

/-- The inverse placement is a piecewise linear homeomorphism of a placed polyhedron. -/
theorem isPLHomeomorphOn_seamWitnessPlaneSymm {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn (⇑seamWitnessPlane.symm) (⇑seamWitnessPlane '' S) S :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_image_seamWitnessPlane hS)
    (isPiecewiseAffineOn_seamWitnessPlaneSymm (isPolyhedron_image_seamWitnessPlane hS))
    (bijOn_seamWitnessPlaneSymm S)

/-! ### Affine maps used to build the model curve -/

/-- The affine functional `(a, t) ↦ a - b` of the coordinate plane. -/
noncomputable def seamShift (b : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ where
  toFun p := p.1 - b
  linear := LinearMap.fst ℝ ℝ ℝ
  map_vadd' p v := by
    simp only [vadd_eq_add, Prod.fst_add, LinearMap.fst_apply]
    ring

/-- Multiplication by a constant, as an affine map of the line. -/
noncomputable def seamScale (c : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun x := c * x
  linear := c • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

/-- The affine functional `a ↦ c * a + d` of the line. -/
noncomputable def seamLine (c d : ℝ) : ℝ →ᵃ[ℝ] ℝ where
  toFun a := c * a + d
  linear := c • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

/-- The projection `(a, t) ↦ t` is piecewise affine on the whole coordinate plane. -/
theorem isPiecewiseAffineOn_seamSnd :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.2) univ :=
  (isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ).congr
    fun _ _ => rfl

/-- The shifted first coordinate is piecewise affine on the whole coordinate plane. -/
theorem isPiecewiseAffineOn_seamShift (b : ℝ) :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => p.1 - b) univ :=
  (isPiecewiseAffineOn_of_affine (seamShift b) isOpen_univ).congr fun _ _ => rfl

/-- The zero function of the coordinate plane is piecewise affine. -/
theorem isPiecewiseAffineOn_seamZero :
    IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
  (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
    fun _ _ => rfl

/-- The zero function of the line is piecewise affine. -/
theorem isPiecewiseAffineOn_seamZeroLine :
    IsPiecewiseAffineOn (fun _ : ℝ => (0 : ℝ)) univ :=
  (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (0 : ℝ)) isOpen_univ).congr fun _ _ => rfl

/-! ### The model source curve -/

/-- One affine ramp of the model source curve: it vanishes for `a ≤ b` and has slope `c`
afterwards. A continuous piecewise affine function of `a` is a sum of such ramps. -/
noncomputable def seamRamp (c b : ℝ) (p : ℝ × ℝ) : ℝ := c * max (p.1 - b) 0

/-- Each ramp is piecewise affine on the whole coordinate plane. -/
theorem isPiecewiseAffineOn_seamRamp (c b : ℝ) : IsPiecewiseAffineOn (seamRamp c b) univ :=
  (((isPiecewiseAffineOn_seamShift b).max isPiecewiseAffineOn_seamZero).affine_comp
    (seamScale c)).congr fun _ _ => rfl

/-- The first coordinate of the model source curve. Its breakpoints are `1`, `3 / 2`, `2`,
`5 / 2` and `7 / 2`. -/
noncomputable def seamArcX (p : ℝ × ℝ) : ℝ :=
  2 - p.1 + seamRamp (-1) 1 p + seamRamp 2 (3 / 2) p + seamRamp (-4) 2 p + seamRamp 6 (5 / 2) p
    + seamRamp (-2) (7 / 2) p

/-- The second coordinate of the model source curve. Its breakpoints are `3 / 2`, `5 / 2`, `3`,
`7 / 2` and `4`. -/
noncomputable def seamArcY (p : ℝ × ℝ) : ℝ :=
  seamRamp (-2) (3 / 2) p + seamRamp 6 (5 / 2) p + seamRamp (-4) 3 p + seamRamp 2 (7 / 2) p
    + seamRamp (-1) 4 p

/-- The model source map of the witness: the source curve swept along the base interval. It
never moves the base coordinate. -/
noncomputable def seamModelMap (p : ℝ × ℝ) : (ℝ × ℝ) × ℝ := ((seamArcX p, seamArcY p), p.2)

/-- The first coordinate of the source curve is piecewise affine. -/
theorem isPiecewiseAffineOn_seamArcX : IsPiecewiseAffineOn seamArcX univ := by
  have h0 : IsPiecewiseAffineOn (fun p : ℝ × ℝ => 2 - p.1) univ :=
    ((isPiecewiseAffineOn_seamShift 2).affine_comp (seamScale (-1))).congr fun _ _ => by
      simp [seamScale]
  exact ((((h0.add (isPiecewiseAffineOn_seamRamp (-1) 1)).add
    (isPiecewiseAffineOn_seamRamp 2 (3 / 2))).add (isPiecewiseAffineOn_seamRamp (-4) 2)).add
      (isPiecewiseAffineOn_seamRamp 6 (5 / 2))).add
        (isPiecewiseAffineOn_seamRamp (-2) (7 / 2))

/-- The second coordinate of the source curve is piecewise affine. -/
theorem isPiecewiseAffineOn_seamArcY : IsPiecewiseAffineOn seamArcY univ :=
  (((((isPiecewiseAffineOn_seamRamp (-2) (3 / 2)).add
    (isPiecewiseAffineOn_seamRamp 6 (5 / 2))).add (isPiecewiseAffineOn_seamRamp (-4) 3)).add
      (isPiecewiseAffineOn_seamRamp 2 (7 / 2))).add (isPiecewiseAffineOn_seamRamp (-1) 4))

/-- The model source map is piecewise affine on the whole coordinate plane. -/
theorem isPiecewiseAffineOn_seamModelMap : IsPiecewiseAffineOn seamModelMap univ :=
  (isPiecewiseAffineOn_seamArcX.prod_mk isPiecewiseAffineOn_seamArcY).prod_mk
    isPiecewiseAffineOn_seamSnd

/-! ### The two bent arc parametrisations -/

/-- The parametrisation of the first bent arc `[e₁, 0] ∪ [0, -e₂]` by `Icc 1 2`. -/
noncomputable def seamBentPos (a : ℝ) : ℝ × ℝ := (max (3 - 2 * a) 0, min (3 - 2 * a) 0)

/-- The parametrisation of the second bent arc `[-e₁, 0] ∪ [0, e₂]` by `Icc 3 4`. -/
noncomputable def seamBentNeg (a : ℝ) : ℝ × ℝ := (min (2 * a - 7) 0, max (2 * a - 7) 0)

/-- The sum of the two coordinates of the first parametrisation recovers the parameter. -/
theorem seamBentPos_sum (a : ℝ) : (seamBentPos a).1 + (seamBentPos a).2 = 3 - 2 * a := by
  simp only [seamBentPos]
  rw [max_add_min]
  ring

/-- The sum of the two coordinates of the second parametrisation recovers the parameter. -/
theorem seamBentNeg_sum (a : ℝ) : (seamBentNeg a).1 + (seamBentNeg a).2 = 2 * a - 7 := by
  simp only [seamBentNeg]
  rw [min_add_max]
  ring

/-- The first parametrisation is piecewise affine. -/
theorem isPiecewiseAffineOn_seamBentPos : IsPiecewiseAffineOn seamBentPos univ := by
  have h : IsPiecewiseAffineOn (fun a : ℝ => 3 - 2 * a) univ :=
    (isPiecewiseAffineOn_of_affine (seamLine (-2) 3) isOpen_univ).congr fun _ _ => by
      simp [seamLine]; ring
  exact ((h.max isPiecewiseAffineOn_seamZeroLine).prod_mk
    (h.min isPiecewiseAffineOn_seamZeroLine))

/-- The second parametrisation is piecewise affine. -/
theorem isPiecewiseAffineOn_seamBentNeg : IsPiecewiseAffineOn seamBentNeg univ := by
  have h : IsPiecewiseAffineOn (fun a : ℝ => 2 * a - 7) univ :=
    (isPiecewiseAffineOn_of_affine (seamLine 2 (-7)) isOpen_univ).congr fun _ _ => by
      simp [seamLine]; ring
  exact ((h.min isPiecewiseAffineOn_seamZeroLine).prod_mk
    (h.max isPiecewiseAffineOn_seamZeroLine))

/-- The first parametrisation is a bijection of `Icc 1 2` onto the first bent arc. -/
theorem bijOn_seamBentPos : BijOn seamBentPos (Icc (1 : ℝ) 2) bentArcPos := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a ⟨h1, h2⟩
    rcases le_total (0 : ℝ) (3 - 2 * a) with hc | hc
    · refine mem_bentArcPos.mpr (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_right hc]
    · refine mem_bentArcPos.mpr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [show (seamBentPos a).1 = max (3 - 2 * a) 0 from rfl, max_eq_right hc]
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentPos a).2 = min (3 - 2 * a) 0 from rfl, min_eq_left hc]
        linarith
  · intro a _ b _ hab
    have h := congrArg (fun q : ℝ × ℝ => q.1 + q.2) hab
    simp only [seamBentPos_sum] at h
    linarith
  · intro p hp
    rw [mem_bentArcPos] at hp
    rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · refine ⟨(3 - p.1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 3 - 2 * ((3 - p.1) / 2) = p.1 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentPos ((3 - p.1) / 2)).1 = max (3 - 2 * ((3 - p.1) / 2)) 0 from rfl,
          hval, max_eq_left h0]
      · rw [show (seamBentPos ((3 - p.1) / 2)).2 = min (3 - 2 * ((3 - p.1) / 2)) 0 from rfl,
          hval, min_eq_right h0, h2]
    · refine ⟨(3 - p.2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 3 - 2 * ((3 - p.2) / 2) = p.2 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentPos ((3 - p.2) / 2)).1 = max (3 - 2 * ((3 - p.2) / 2)) 0 from rfl,
          hval, max_eq_right h2, h1]
      · rw [show (seamBentPos ((3 - p.2) / 2)).2 = min (3 - 2 * ((3 - p.2) / 2)) 0 from rfl,
          hval, min_eq_left h2]

/-- The second parametrisation is a bijection of `Icc 3 4` onto the second bent arc. -/
theorem bijOn_seamBentNeg : BijOn seamBentNeg (Icc (3 : ℝ) 4) bentArcNeg := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a ⟨h1, h2⟩
    rcases le_total (2 * a - 7) (0 : ℝ) with hc | hc
    · refine mem_bentArcNeg.mpr (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_right hc]
    · refine mem_bentArcNeg.mpr (Or.inr ⟨?_, ?_, ?_⟩)
      · rw [show (seamBentNeg a).1 = min (2 * a - 7) 0 from rfl, min_eq_right hc]
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_left hc]
        linarith
      · rw [show (seamBentNeg a).2 = max (2 * a - 7) 0 from rfl, max_eq_left hc]
        linarith
  · intro a _ b _ hab
    have h := congrArg (fun q : ℝ × ℝ => q.1 + q.2) hab
    simp only [seamBentNeg_sum] at h
    linarith
  · intro p hp
    rw [mem_bentArcNeg] at hp
    rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · refine ⟨(p.1 + 7) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 2 * ((p.1 + 7) / 2) - 7 = p.1 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentNeg ((p.1 + 7) / 2)).1 = min (2 * ((p.1 + 7) / 2) - 7) 0 from rfl,
          hval, min_eq_left h1]
      · rw [show (seamBentNeg ((p.1 + 7) / 2)).2 = max (2 * ((p.1 + 7) / 2) - 7) 0 from rfl,
          hval, max_eq_right h1, h2]
    · refine ⟨(p.2 + 7) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hval : 2 * ((p.2 + 7) / 2) - 7 = p.2 := by ring
      refine Prod.ext ?_ ?_
      · rw [show (seamBentNeg ((p.2 + 7) / 2)).1 = min (2 * ((p.2 + 7) / 2) - 7) 0 from rfl,
          hval, min_eq_right h0, h1]
      · rw [show (seamBentNeg ((p.2 + 7) / 2)).2 = max (2 * ((p.2 + 7) / 2) - 7) 0 from rfl,
          hval, max_eq_left h0]

/-- The first parametrisation is a piecewise linear homeomorphism onto the first bent arc. -/
theorem isPLHomeomorphOn_seamBentPos :
    IsPLHomeomorphOn seamBentPos (Icc (1 : ℝ) 2) bentArcPos :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_seamBentPos.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron
      (subset_univ _)) bijOn_seamBentPos

/-- The second parametrisation is a piecewise linear homeomorphism onto the second bent arc. -/
theorem isPLHomeomorphOn_seamBentNeg :
    IsPLHomeomorphOn seamBentNeg (Icc (3 : ℝ) 4) bentArcNeg :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_seamBentNeg.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron
      (subset_univ _)) bijOn_seamBentNeg

/-- The first bent arc parametrisation at the left wall. -/
theorem seamBentPos_one : seamBentPos 1 = ((1 : ℝ), (0 : ℝ)) := by
  have h : (3 : ℝ) - 2 * 1 = 1 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_eq_left zero_le_one) (min_eq_right zero_le_one)

/-- The first bent arc parametrisation at the right wall. -/
theorem seamBentPos_two : seamBentPos 2 = ((0 : ℝ), (-1 : ℝ)) := by
  have h : (3 : ℝ) - 2 * 2 = -1 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_eq_right (by norm_num)) (min_eq_left (by norm_num))

/-- The first bent arc parametrisation at the centre of the cross section. -/
theorem seamBentPos_mid : seamBentPos (3 / 2) = ((0 : ℝ), (0 : ℝ)) := by
  have h : (3 : ℝ) - 2 * (3 / 2) = 0 := by norm_num
  simp only [seamBentPos, h]
  exact Prod.ext (max_self 0) (min_self 0)

/-- The second bent arc parametrisation at the left wall. -/
theorem seamBentNeg_three : seamBentNeg 3 = ((-1 : ℝ), (0 : ℝ)) := by
  have h : (2 : ℝ) * 3 - 7 = -1 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_eq_left (by norm_num)) (max_eq_right (by norm_num))

/-- The second bent arc parametrisation at the right wall. -/
theorem seamBentNeg_four : seamBentNeg 4 = ((0 : ℝ), (1 : ℝ)) := by
  have h : (2 : ℝ) * 4 - 7 = 1 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_eq_right zero_le_one) (max_eq_left zero_le_one)

/-- The second bent arc parametrisation at the centre of the cross section. -/
theorem seamBentNeg_mid : seamBentNeg (7 / 2) = ((0 : ℝ), (0 : ℝ)) := by
  have h : (2 : ℝ) * (7 / 2) - 7 = 0 := by norm_num
  simp only [seamBentNeg, h]
  exact Prod.ext (min_self 0) (max_self 0)

/-- The left wall value of the first arc lies on the lateral boundary. -/
theorem seamBentPos_one_mem : seamBentPos 1 ∈ spliceSquareBoundary := by
  rw [seamBentPos_one]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩

/-- The right wall value of the first arc lies on the lateral boundary. -/
theorem seamBentPos_two_mem : seamBentPos 2 ∈ spliceSquareBoundary := by
  rw [seamBentPos_two]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩

/-- The left wall value of the second arc lies on the lateral boundary. -/
theorem seamBentNeg_three_mem : seamBentNeg 3 ∈ spliceSquareBoundary := by
  rw [seamBentNeg_three]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inl rfl⟩

/-- The right wall value of the second arc lies on the lateral boundary. -/
theorem seamBentNeg_four_mem : seamBentNeg 4 ∈ spliceSquareBoundary := by
  rw [seamBentNeg_four]
  exact ⟨by rw [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩

/-! ### The two source sheet maps -/

/-- The first source sheet map: the first bent arc parametrisation swept along the base. -/
noncomputable def seamSheetPos : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := Prod.map seamBentPos id

/-- The second source sheet map. -/
noncomputable def seamSheetNeg : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := Prod.map seamBentNeg id

/-- The first source band is carried piecewise linearly onto the first bent sheet. -/
theorem isPLHomeomorphOn_seamSheetPos :
    IsPLHomeomorphOn seamSheetPos (Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1) bentSheetPos :=
  isPLHomeomorphOn_seamBentPos.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

/-- The second source band is carried piecewise linearly onto the second bent sheet. -/
theorem isPLHomeomorphOn_seamSheetNeg :
    IsPLHomeomorphOn seamSheetNeg (Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1) bentSheetNeg :=
  isPLHomeomorphOn_seamBentNeg.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

/-! ### Evaluating the model curve band by band -/

/-- On the first face band the source curve runs inward to the wall value `e₁`. -/
theorem seamArcX_lowFace {p : ℝ × ℝ} (h1 : p.1 ≤ 1) : seamArcX p = 2 - p.1 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_right (by linarith : p.1 - 1 ≤ 0), max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 2 ≤ 0), max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0)]
  ring

/-- On the first source band the source curve is the first bent arc parametrisation. -/
theorem seamArcX_bandPos {p : ℝ × ℝ} (h1 : 1 ≤ p.1) (h2 : p.1 ≤ 2) :
    seamArcX p = max (3 - 2 * p.1) 0 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_right (by linarith : p.1 - 2 ≤ 0), max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0)]
  rcases le_total p.1 (3 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ 3 - 2 * p.1)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
      max_eq_right (by linarith : 3 - 2 * p.1 ≤ 0)]
    ring

/-- On the first source band the second coordinate is the second coordinate of the first bent
arc parametrisation. -/
theorem seamArcY_bandPos {p : ℝ × ℝ} (h2 : p.1 ≤ 2) :
    seamArcY p = min (3 - 2 * p.1) 0 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  rcases le_total p.1 (3 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 3 / 2 ≤ 0),
      min_eq_right (by linarith : (0 : ℝ) ≤ 3 - 2 * p.1)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
      min_eq_left (by linarith : 3 - 2 * p.1 ≤ 0)]
    ring

/-- On the lower half of the connector band the curve descends below the cross section
square. -/
theorem seamArcY_connectorLow {p : ℝ × ℝ} (h1 : 2 ≤ p.1) (h2 : p.1 ≤ 5 / 2) :
    seamArcY p = 3 - 2 * p.1 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_right (by linarith : p.1 - 5 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 3 ≤ 0),
    max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0), max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  ring

/-- On the upper half of the connector band the curve returns to the left of the cross section
square. -/
theorem seamArcX_connectorHigh {p : ℝ × ℝ} (h1 : 5 / 2 ≤ p.1) (h2 : p.1 ≤ 3) :
    seamArcX p = 2 * p.1 - 7 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_right (by linarith [h2] : p.1 - 7 / 2 ≤ 0)]
  ring

/-- On the second source band the source curve is the second bent arc parametrisation. -/
theorem seamArcX_bandNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) :
    seamArcX p = min (2 * p.1 - 7) 0 := by
  simp only [seamArcX, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 1),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2)]
  rcases le_total p.1 (7 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
      min_eq_left (by linarith : 2 * p.1 - 7 ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
      min_eq_right (by linarith : (0 : ℝ) ≤ 2 * p.1 - 7)]
    ring

/-- On the second source band the second coordinate is the second coordinate of the second
bent arc parametrisation. -/
theorem seamArcY_bandNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) (h2 : p.1 ≤ 4) :
    seamArcY p = max (2 * p.1 - 7) 0 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3),
    max_eq_right (by linarith : p.1 - 4 ≤ 0)]
  rcases le_total p.1 (7 / 2) with hc | hc
  · rw [max_eq_right (by linarith : p.1 - 7 / 2 ≤ 0),
      max_eq_right (by linarith : 2 * p.1 - 7 ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
      max_eq_left (by linarith : (0 : ℝ) ≤ 2 * p.1 - 7)]
    ring

/-- On the last face band the source curve runs outward from the wall value `e₂`. -/
theorem seamArcY_highFace {p : ℝ × ℝ} (h1 : 4 ≤ p.1) :
    seamArcY p = p.1 - 3 := by
  simp only [seamArcY, seamRamp]
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 5 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 3),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 7 / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ p.1 - 4)]
  ring

/-- On the first source band the model source map is the first source sheet map. -/
theorem seamModelMap_eq_seamSheetPos {p : ℝ × ℝ} (h1 : 1 ≤ p.1) (h2 : p.1 ≤ 2) :
    seamModelMap p = seamSheetPos p :=
  Prod.ext (Prod.ext (seamArcX_bandPos h1 h2) (seamArcY_bandPos h2)) rfl

/-- On the second source band the model source map is the second source sheet map. -/
theorem seamModelMap_eq_seamSheetNeg {p : ℝ × ℝ} (h1 : 3 ≤ p.1) (h2 : p.1 ≤ 4) :
    seamModelMap p = seamSheetNeg p :=
  Prod.ext (Prod.ext (seamArcX_bandNeg h1) (seamArcY_bandNeg h1 h2)) rfl

/-! ### The source curve leaves the cross section square off the two source bands -/

/-- Off the two source bands the model source map leaves the parametrised cylinder. Each of the
three face bands escapes through a different side of the cross section square. -/
theorem seamModelMap_notMem_spliceCylinder {p : ℝ × ℝ}
    (hpos : ¬(1 ≤ p.1 ∧ p.1 ≤ 2)) (hneg : ¬(3 ≤ p.1 ∧ p.1 ≤ 4)) :
    seamModelMap p ∉ spliceCylinder := by
  intro hmem
  have hsq : (seamArcX p, seamArcY p) ∈ spliceSquare := hmem.1
  rw [mem_spliceSquare] at hsq
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hsq
  rcases lt_or_ge p.1 1 with ha | ha
  · rw [seamArcX_lowFace (le_of_lt ha)] at hx2
    linarith
  rcases le_or_gt p.1 2 with hb | hb
  · exact hpos ⟨ha, hb⟩
  rcases lt_or_ge p.1 3 with hc | hc
  · rcases le_or_gt p.1 (5 / 2) with hd | hd
    · rw [seamArcY_connectorLow (le_of_lt hb) hd] at hy1
      linarith
    · rw [seamArcX_connectorHigh (le_of_lt hd) (le_of_lt hc)] at hx1
      linarith
  rcases le_or_gt p.1 4 with he | he
  · exact hneg ⟨hc, he⟩
  · rw [seamArcY_highFace (le_of_lt he)] at hy2
    linarith

/-! ### The source rectangles -/

/-- The source disk of the witness. -/
def seamSourceRect : Set (ℝ × ℝ) := Icc (0 : ℝ) 5 ×ˢ Icc (0 : ℝ) 1

/-- The first source band of the witness. -/
def seamRectPos : Set (ℝ × ℝ) := Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1

/-- The second source band of the witness. -/
def seamRectNeg : Set (ℝ × ℝ) := Icc (3 : ℝ) 4 ×ˢ Icc (0 : ℝ) 1

/-- The three complementary bands of the witness. -/
def seamFaceRect : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∪ Icc (2 : ℝ) 3 ×ˢ Icc (0 : ℝ) 1 ∪
    Icc (4 : ℝ) 5 ×ˢ Icc (0 : ℝ) 1

/-- The source disk of the witness is a polyhedron. -/
theorem isPolyhedron_seamSourceRect : IsPolyhedron seamSourceRect :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

/-- The first source band is a polyhedron. -/
theorem isPolyhedron_seamRectPos : IsPolyhedron seamRectPos :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

/-- The second source band is a polyhedron. -/
theorem isPolyhedron_seamRectNeg : IsPolyhedron seamRectNeg :=
  (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron

/-- The complementary bands form a polyhedron. -/
theorem isPolyhedron_seamFaceRect : IsPolyhedron seamFaceRect :=
  (((isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron.union
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron).union
      (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron)

/-- The source disk of the witness is a piecewise linear two ball. -/
theorem isPLBall_seamSourceRect : IsPLBall 2 seamSourceRect :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

/-- The five bands cover the source disk. -/
theorem seamRect_union : seamRectPos ∪ seamRectNeg ∪ seamFaceRect = seamSourceRect := by
  apply Subset.antisymm
  · intro p hp
    rcases hp with (h | h) | ((h | h) | h) <;>
      exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩
  · rintro p ⟨⟨h0, h5⟩, ht⟩
    rcases le_or_gt p.1 1 with h | h
    · exact Or.inr (Or.inl (Or.inl ⟨⟨h0, h⟩, ht⟩))
    rcases le_or_gt p.1 2 with h' | h'
    · exact Or.inl (Or.inl ⟨⟨le_of_lt h, h'⟩, ht⟩)
    rcases le_or_gt p.1 3 with h'' | h''
    · exact Or.inr (Or.inl (Or.inr ⟨⟨le_of_lt h', h''⟩, ht⟩))
    rcases le_or_gt p.1 4 with h''' | h'''
    · exact Or.inl (Or.inr ⟨⟨le_of_lt h'', h'''⟩, ht⟩)
    · exact Or.inr (Or.inr ⟨⟨le_of_lt h''', h5⟩, ht⟩)

/-! ### The model cell -/

/-- **The model cross reglued cell of the witness.** It is the model source map of the witness,
placed in the model three space. -/
noncomputable def seamWitnessCell : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) where
  domain := ⇑seamWitnessPlane '' seamSourceRect
  isPLBall_domain :=
    isPLBall_seamSourceRect.of_isPLHomeomorphOn
      (isPLHomeomorphOn_seamWitnessPlane isPolyhedron_seamSourceRect)
  toFun := ⇑spliceEmbedding ∘ seamModelMap ∘ ⇑seamWitnessPlane.symm
  isPLOn := by
    have hdom : IsPolyhedron (⇑seamWitnessPlane '' seamSourceRect) :=
      isPolyhedron_image_seamWitnessPlane isPolyhedron_seamSourceRect
    have hcomp : IsPiecewiseAffineOn (seamModelMap ∘ ⇑seamWitnessPlane.symm)
        (⇑seamWitnessPlane '' seamSourceRect) := by
      have h := isPiecewiseAffineOn_seamModelMap.comp
        (isPiecewiseAffineOn_seamWitnessPlaneSymm hdom)
      rwa [preimage_univ, inter_univ] at h
    have hpa : IsPiecewiseAffineOn
        (⇑spliceEmbedding ∘ seamModelMap ∘ ⇑seamWitnessPlane.symm)
        (⇑seamWitnessPlane '' seamSourceRect) :=
      (hcomp.affine_comp spliceEmbedding.toLinearMap.toAffineMap).congr fun _ _ => rfl
    exact fun x hx => ⟨hpa.continuousOn x hx, hpa x hx⟩

/-- The model cell of the witness, evaluated. -/
theorem seamWitnessCell_apply (x : EuclideanSpace ℝ (Fin 2)) :
    seamWitnessCell x = spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) := rfl

/-- The source disk of the model cell of the witness. -/
theorem seamWitnessCell_domain :
    seamWitnessCell.domain = ⇑seamWitnessPlane '' seamSourceRect := rfl

/-! ### The tagged coordinate of the witness -/

/-- **The tagged model coordinate of the witness.** The two source bands are separated by the
test `a ≤ 2`, so the sheet label is constant on each of them. -/
noncomputable def seamWitnessCoord (x : EuclideanSpace ℝ (Fin 2)) : Bool × ((ℝ × ℝ) × ℝ) :=
  if (seamWitnessPlane.symm x).1 ≤ 2 then (true, seamSheetPos (seamWitnessPlane.symm x))
  else (false, seamSheetNeg (seamWitnessPlane.symm x))

/-- On the first source band the tagged coordinate is the first source sheet map. -/
theorem seamWitnessCoord_of_mem_pos {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ ⇑seamWitnessPlane '' seamRectPos) :
    seamWitnessCoord x = (true, seamSheetPos (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact if_pos h.1.2

/-- On the second source band the tagged coordinate is the second source sheet map. -/
theorem seamWitnessCoord_of_mem_neg {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ ⇑seamWitnessPlane '' seamRectNeg) :
    seamWitnessCoord x = (false, seamSheetNeg (seamWitnessPlane.symm x)) := by
  have h := mem_image_seamWitnessPlane.mp hx
  exact if_neg (by linarith [h.1.1] : ¬(seamWitnessPlane.symm x).1 ≤ 2)

/-! ### The frontier of the source disk -/

/-- The frontier of the source disk of the witness, in the coordinate plane. -/
theorem frontier_seamSourceRect :
    frontier seamSourceRect = seamSourceRect \ Ioo (0 : ℝ) 5 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [isPolyhedron_seamSourceRect.isClosed.frontier_eq, seamSourceRect, interior_prod_eq,
    interior_Icc, interior_Icc]

/-- The frontier of the source disk of the witness. -/
theorem frontier_seamWitnessCell_domain :
    frontier seamWitnessCell.domain = ⇑seamWitnessPlane '' frontier seamSourceRect :=
  (seamWitnessPlane.toHomeomorph.image_frontier seamSourceRect).symm

/-! ### The reading -/

/-- **The piecewise linear reading of the model cross reglue.** -/
noncomputable def seamWitnessReading :
    PLCrossSeamReading (⇑spliceEmbedding) seamWitnessCell where
  coord := seamWitnessCoord
  sourcePos := ⇑seamWitnessPlane '' seamRectPos
  sourceNeg := ⇑seamWitnessPlane '' seamRectNeg
  face := ⇑seamWitnessPlane '' seamFaceRect
  isPLHomeomorphOn_pos :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm isPolyhedron_seamRectPos).trans
      isPLHomeomorphOn_seamSheetPos).congr fun x hx => by
        rw [seamWitnessCoord_of_mem_pos hx]
        rfl
  isPLHomeomorphOn_neg :=
    ((isPLHomeomorphOn_seamWitnessPlaneSymm isPolyhedron_seamRectNeg).trans
      isPLHomeomorphOn_seamSheetNeg).congr fun x hx => by
        rw [seamWitnessCoord_of_mem_neg hx]
        rfl
  coord_fst_pos := fun x hx => by rw [seamWitnessCoord_of_mem_pos hx]
  coord_fst_neg := fun x hx => by rw [seamWitnessCoord_of_mem_neg hx]
  source_eq := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · have h := mem_image_seamWitnessPlane.mp hx
        refine ⟨mem_image_seamWitnessPlane.mpr ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
          h.2⟩, ?_⟩
        refine ⟨seamModelMap (seamWitnessPlane.symm x), ?_, rfl⟩
        rw [seamModelMap_eq_seamSheetPos h.1.1 h.1.2]
        exact ⟨bentArcPos_subset_spliceSquare
          (isPLHomeomorphOn_seamBentPos.bijOn.mapsTo h.1), h.2⟩
      · have h := mem_image_seamWitnessPlane.mp hx
        refine ⟨mem_image_seamWitnessPlane.mpr ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
          h.2⟩, ?_⟩
        refine ⟨seamModelMap (seamWitnessPlane.symm x), ?_, rfl⟩
        rw [seamModelMap_eq_seamSheetNeg h.1.1 h.1.2]
        exact ⟨bentArcNeg_subset_spliceSquare
          (isPLHomeomorphOn_seamBentNeg.bijOn.mapsTo h.1), h.2⟩
    · rintro x ⟨hxd, hxc⟩
      have hd := mem_image_seamWitnessPlane.mp hxd
      have hcyl : seamModelMap (seamWitnessPlane.symm x) ∈ spliceCylinder := by
        obtain ⟨q, hq, hqe⟩ := hxc
        have : q = seamModelMap (seamWitnessPlane.symm x) := spliceEmbedding.injective hqe
        rwa [← this]
      by_cases hpos : 1 ≤ (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 ≤ 2
      · exact Or.inl (mem_image_seamWitnessPlane.mpr ⟨hpos, hd.2⟩)
      by_cases hneg : 3 ≤ (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 ≤ 4
      · exact Or.inr (mem_image_seamWitnessPlane.mpr ⟨hneg, hd.2⟩)
      · exact absurd hcyl (seamModelMap_notMem_spliceCylinder hpos hneg)
  isPolyhedron_face := isPolyhedron_image_seamWitnessPlane isPolyhedron_seamFaceRect
  union_eq := by
    rw [← image_union, ← image_union, seamRect_union]
    rfl
  reglued_eq := by
    rintro x (hx | hx)
    · have h := mem_image_seamWitnessPlane.mp hx
      rw [seamWitnessCell_apply]
      change spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) =
        spliceEmbedding (crossSeamInclude (seamWitnessCoord x))
      rw [seamWitnessCoord_of_mem_pos hx, seamModelMap_eq_seamSheetPos h.1.1 h.1.2]
      rfl
    · have h := mem_image_seamWitnessPlane.mp hx
      rw [seamWitnessCell_apply]
      change spliceEmbedding (seamModelMap (seamWitnessPlane.symm x)) =
        spliceEmbedding (crossSeamInclude (seamWitnessCoord x))
      rw [seamWitnessCoord_of_mem_neg hx, seamModelMap_eq_seamSheetNeg h.1.1 h.1.2]
      rfl
  overlap_lateral := by
    rintro x ⟨hx | hx, hf⟩
    · have h := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [seamWitnessCoord_of_mem_pos hx]
      refine ⟨?_, h.2⟩
      change seamBentPos (seamWitnessPlane.symm x).1 ∈ spliceSquareBoundary
      rcases hface with (⟨⟨-, hb⟩, -⟩ | ⟨⟨hb, -⟩, -⟩) | ⟨⟨hb, -⟩, -⟩
      · rw [le_antisymm hb h.1.1]
        exact seamBentPos_one_mem
      · rw [le_antisymm h.1.2 hb]
        exact seamBentPos_two_mem
      · exact absurd h.1.2 (by linarith)
    · have h := mem_image_seamWitnessPlane.mp hx
      have hface := mem_image_seamWitnessPlane.mp hf
      rw [seamWitnessCoord_of_mem_neg hx]
      refine ⟨?_, h.2⟩
      change seamBentNeg (seamWitnessPlane.symm x).1 ∈ spliceSquareBoundary
      rcases hface with (⟨⟨-, hb⟩, -⟩ | ⟨⟨-, hb⟩, -⟩) | ⟨⟨hb, -⟩, -⟩
      · exact absurd h.1.1 (by linarith)
      · rw [le_antisymm hb h.1.1]
        exact seamBentNeg_three_mem
      · rw [le_antisymm h.1.2 hb]
        exact seamBentNeg_four_mem
  boundary_iff_end := by
    intro x hx
    have hband : 0 < (seamWitnessPlane.symm x).1 ∧ (seamWitnessPlane.symm x).1 < 5 ∧
        (seamWitnessPlane.symm x).2 ∈ Icc (0 : ℝ) 1 := by
      rcases hx with hx | hx
      · have h := mem_image_seamWitnessPlane.mp hx
        exact ⟨by linarith [h.1.1], by linarith [h.1.2], h.2⟩
      · have h := mem_image_seamWitnessPlane.mp hx
        exact ⟨by linarith [h.1.1], by linarith [h.1.2], h.2⟩
    have hcoord : (seamWitnessCoord x).2.2 = (seamWitnessPlane.symm x).2 := by
      rcases hx with hx | hx
      · rw [seamWitnessCoord_of_mem_pos hx]; rfl
      · rw [seamWitnessCoord_of_mem_neg hx]; rfl
    rw [hcoord, frontier_seamWitnessCell_domain, mem_image_seamWitnessPlane,
      frontier_seamSourceRect]
    constructor
    · rintro ⟨-, hout⟩
      by_contra hcon
      rw [not_or] at hcon
      exact hout ⟨⟨hband.1, hband.2.1⟩,
        lt_of_le_of_ne hband.2.2.1 (Ne.symm hcon.1),
        lt_of_le_of_ne hband.2.2.2 hcon.2⟩
    · intro hend
      refine ⟨⟨⟨le_of_lt hband.1, le_of_lt hband.2.1⟩, hband.2.2⟩, ?_⟩
      rintro ⟨-, ht1, ht2⟩
      rcases hend with h | h
      · rw [h] at ht1; exact absurd ht1 (lt_irrefl 0)
      · rw [h] at ht2; exact absurd ht2 (lt_irrefl 1)

/-- **The piecewise linear reading of the cross reglue is not vacuous.** -/
theorem nonempty_plCrossSeamReading_seamWitnessCell :
    Nonempty (PLCrossSeamReading (⇑spliceEmbedding) seamWitnessCell) :=
  ⟨seamWitnessReading⟩

/-! ### The witness is not degenerate -/

/-- The first source band of the witness is nonempty. -/
theorem seamWitnessReading_sourcePos_nonempty : seamWitnessReading.sourcePos.Nonempty :=
  seamWitnessReading.sourcePos_nonempty

/-- The second source band of the witness is nonempty. -/
theorem seamWitnessReading_sourceNeg_nonempty : seamWitnessReading.sourceNeg.Nonempty :=
  seamWitnessReading.sourceNeg_nonempty

/-- The complementary face of the witness is nonempty. -/
theorem seamWitnessReading_face_nonempty : seamWitnessReading.face.Nonempty :=
  seamWitnessReading.face_nonempty

/-- The part of the source disk of the witness lying over the tube is a proper part of it. -/
theorem seamWitnessReading_tubeSource_ssubset :
    seamWitnessReading.tubeSource ⊂ seamWitnessCell.domain :=
  seamWitnessReading.source_ssubset_domain

/-- The centre of the first source band. -/
theorem seamWitnessPoint_pos_mem :
    seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ)) ∈ seamWitnessReading.sourcePos :=
  ⟨((3 / 2 : ℝ), (0 : ℝ)), ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, rfl⟩

/-- The centre of the second source band. -/
theorem seamWitnessPoint_neg_mem :
    seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ)) ∈ seamWitnessReading.sourceNeg :=
  ⟨((7 / 2 : ℝ), (0 : ℝ)), ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, rfl⟩

/-- The two source bands are carried to the centre of the cross section at the same level: the
witness really is a touching seam. -/
theorem seamWitnessCell_apply_pos :
    seamWitnessCell (seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ))) =
      spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
  have hval : seamSheetPos ((3 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
    change (seamBentPos (3 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ))
    rw [seamBentPos_mid]
  rw [seamWitnessCell_apply, seamWitnessPlane.symm_apply_apply,
    seamModelMap_eq_seamSheetPos (by norm_num) (by norm_num), hval]

/-- The second source band reaches the same point. -/
theorem seamWitnessCell_apply_neg :
    seamWitnessCell (seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ))) =
      spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
  have hval : seamSheetNeg ((7 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
    change (seamBentNeg (7 / 2 : ℝ), (0 : ℝ)) = (((0 : ℝ), (0 : ℝ)), (0 : ℝ))
    rw [seamBentNeg_mid]
  rw [seamWitnessCell_apply, seamWitnessPlane.symm_apply_apply,
    seamModelMap_eq_seamSheetNeg (by norm_num) (by norm_num), hval]

/-- **The witness has a double point inside the tube.** The two bent sheets meet at the centre
of the cross section, which is exactly the defect that the seam resolution removes. -/
theorem mem_doublePointSet_seamWitnessCell :
    spliceEmbedding (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈
      doublePointSet seamWitnessCell seamWitnessReading.tubeSource := by
  refine ⟨seamWitnessPlane ((3 / 2 : ℝ), (0 : ℝ)),
    seamWitnessReading.mem_tubeSource.mpr (Or.inl seamWitnessPoint_pos_mem),
    seamWitnessPlane ((7 / 2 : ℝ), (0 : ℝ)),
    seamWitnessReading.mem_tubeSource.mpr (Or.inr seamWitnessPoint_neg_mem), ?_,
    seamWitnessCell_apply_pos, seamWitnessCell_apply_neg⟩
  intro h
  have h' : ((3 / 2 : ℝ), (0 : ℝ)) = ((7 / 2 : ℝ), (0 : ℝ)) := seamWitnessPlane.injective h
  exact absurd (congrArg Prod.fst h') (by norm_num)

/-- **The witness cell is not injective.** -/
theorem seamWitnessCell_notInjOn :
    ¬InjOn seamWitnessCell seamWitnessCell.domain := by
  intro hinj
  have hpos := seamWitnessReading.source_subset_domain
    (seamWitnessReading.mem_tubeSource.mpr (Or.inl seamWitnessPoint_pos_mem))
  have hneg := seamWitnessReading.source_subset_domain
    (seamWitnessReading.mem_tubeSource.mpr (Or.inr seamWitnessPoint_neg_mem))
  have h := hinj hpos hneg (seamWitnessCell_apply_pos.trans seamWitnessCell_apply_neg.symm)
  have h' : ((3 / 2 : ℝ), (0 : ℝ)) = ((7 / 2 : ℝ), (0 : ℝ)) := seamWitnessPlane.injective h
  exact absurd (congrArg Prod.fst h') (by norm_num)

/-- **The resolved cell of the witness has no double point over the tube.** Over the very same
part of the source disk on which the cross reglue has the double point
`mem_doublePointSet_seamWitnessCell`, the constructed resolution has none: a touching seam goes
in and no double point comes out. A tube chart to build the resolution with is supplied by
`nonempty_plSeamTubeChart_spliceEmbedding`. -/
theorem doublePointSet_resolvedCell_seamWitness
    (C : PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding) :
    doublePointSet (seamWitnessReading.resolvedCell C) seamWitnessReading.tubeSource = ∅ :=
  seamWitnessReading.doublePointSet_resolvedCell C

end DifferentialGeometry.Topology.PiecewiseLinear
