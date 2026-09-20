/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

/-!
# Resolving the transverse cross around a closed branch

The first closed branch case of Moise's Lemma 2 has a branch circle whose complete preimage is
a single circle doubly covering it. `CylinderSplice` models a tube around such a branch as the
square cylinder `spliceSquare ×ˢ Icc 0 1` glued by `SpliceRel`, whose end map is `Prod.swap`.
The old configuration is the transverse cross `crossingArcX ∪ crossingArcY` swept around the
circle, and Moise's replacement is the pair of disjoint chords `spliceArcPos`, `spliceArcNeg`,
the traces of `x - y = 1` and `x - y = -1`.

This file is the closed branch analogue of `LoopTheorem.CrossSeamResolution`. There the base is
an interval, the resolution is a product along it, and the two chords never interact. Here the
base is a circle, and the period map `Prod.swap` *exchanges* the two chords, so the replacement
is one band that closes up only after two periods.

* `closedSeamSource` is the source annulus, presented as the fundamental domain
  `Icc (-1) 1 ×ˢ Ico 0 2`: the transverse parameter runs over `[-1, 1]` and the base parameter
  over two periods of the branch circle, the second period end being the identified copy of
  the first. `closedSeamInclude` is the old crossing configuration read on it and
  `closedSeamResolve` is Moise's replacement.
* `doublePointSet_closedSeamInclude` and `doublePointSet_closedSeamResolve` are the exact form
  of the deletion: the crossing configuration swept around the circle has the image of the core
  curve as its double point set, at every level of the tube, and the replacement has none.
  `image_closedSeamInclude` and `image_closedSeamResolve` record that the two maps cover the
  two figures, so that the second statement is not empty for want of an image.
* `closedSeamResolve_eq_iff` is the sense in which the replacement is an annulus and not a
  Möbius band: on the closed rectangle `closedSeamRect` the replacement identifies exactly the
  pairs `(s, 0)` and `(s, 2)`, with the same transverse parameter `s`. The twisted
  identification fails, by `closedSeamResolve_top_ne_reflected_bottom`.
* `swap_image_spliceArcPos_ne_self`, `swap_comp_swap_eqOn_spliceArcPos` and
  `exists_spliceArcFlip_ne_self` are the local reason: the period map carries each chord to the
  other, so the two chords are a single orbit, and two periods return each chord to itself by
  the identity, not by the endpoint exchanging flip `spliceArcFlip`.
* `swap_image_spliceSumArcPos` and `exists_swap_ne_self_mem_spliceSumArcPos` record why the
  other pair of chords, `x + y = 1` and `x + y = -1`, is the wrong choice here even though
  `spliceSumArc_inter_spliceSquareBoundary` shows it has the same four lateral endpoints: the
  period map preserves each of those chords and exchanges its two endpoints, so each would
  close up into a Möbius band.

Not proved here, and deliberately out of scope: that an actual closed branch carries a
cylindrical diagram over a triangulated square whose end map is `Prod.swap`, and the
straightening of an arbitrary piecewise linear monodromy to `Prod.swap`. Determining which
rays the monodromy permutes is not the same as obtaining a pointwise normal form, and the
straightening is substantive geometry that is missing from the tree.

Also not proved here: a piecewise linear homeomorphism from a standard annulus onto the image
of the replacement figure. The target `Quotient spliceSetoid` carries no topology and no
piecewise linear structure in this tree, so `IsPLBall` and `IsPLHomeomorphOn` cannot be stated
about it at all. What `closedSeamResolve_eq_iff` gives instead is the exact identification
pattern of the piecewise linear rectangle `closedSeamRect`, which is the set level content of
the word annulus, together with `isPLBall_closedSeamRect` for the rectangle itself.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-! ### Points of the spliced cylinder away from the top level -/

/-- Two points of the unglued cylinder whose base coordinates are both different from `1`
have the same image in the spliced cylinder only if they are equal: the period identification
always uses the top level. -/
theorem eq_of_spliceMk_eq_of_snd_ne_one {p q : (ℝ × ℝ) × ℝ} (hp : p.2 ≠ 1) (hq : q.2 ≠ 1)
    (h : spliceMk p = spliceMk q) : p = q := by
  rcases spliceMk_eq_iff.mp h with h' | ⟨-, h1, -⟩ | ⟨h1, -, -⟩
  · exact h'
  · exact absurd h1 hq
  · exact absurd h1 hp

/-- The image of the core curve is already covered by the base parameters below `1`, because
the period map fixes the centre of the square. -/
theorem image_spliceCore_eq_image_Ico :
    spliceMk '' spliceCore
      = spliceMk '' (({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ×ˢ Ico (0 : ℝ) 1) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨hz1, hz2⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hz1
    rw [Set.mem_Icc] at hz2
    rcases lt_or_eq_of_le hz2.2 with hlt | heq
    · exact ⟨z, ⟨hz1, Set.mem_Ico.mpr ⟨hz2.1, hlt⟩⟩, rfl⟩
    · refine ⟨(((0 : ℝ), (0 : ℝ)), (0 : ℝ)), ⟨rfl, Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩⟩, ?_⟩
      have hz : z = (((0 : ℝ), (0 : ℝ)), (1 : ℝ)) := Prod.ext hz1 heq
      rw [hz]
      exact spliceMk_core_zero_eq_one
  · rintro y ⟨z, ⟨hz1, hz2⟩, rfl⟩
    exact ⟨z, ⟨hz1, Set.Ico_subset_Icc_self hz2⟩, rfl⟩

/-! ### The two chords are a single orbit of the period map -/

/-- The period map carries the chord `x - y = -1` back to the chord `x - y = 1`, so together
with `swap_image_spliceArcPos` the two chords form a single orbit of the period map. -/
theorem swap_image_spliceArcNeg : Prod.swap '' spliceArcNeg = spliceArcPos := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_spliceArcPos_of_mem_spliceArcNeg hq
  · intro p hp
    exact ⟨p.swap, swap_mem_spliceArcNeg_of_mem_spliceArcPos hp, Prod.swap_swap p⟩

/-- The orbit is not a fixed point: one period really moves the chord `x - y = 1` off itself,
so a point of the replacement needs two periods to return to its own chord. -/
theorem swap_image_spliceArcPos_ne_self : Prod.swap '' spliceArcPos ≠ spliceArcPos := by
  rw [swap_image_spliceArcPos]
  exact fun h => spliceArcPos_ne_spliceArcNeg h.symm

/-- The endpoint exchanging affine involution of the chord `x - y = 1`, the flip that a Möbius
band would induce after two periods. -/
def spliceArcFlip (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, -p.1)

/-- Value of the flip of the chord `x - y = 1`. -/
theorem spliceArcFlip_apply (p : ℝ × ℝ) : spliceArcFlip p = (-p.2, -p.1) := rfl

/-- The flip carries the chord `x - y = 1` to itself. -/
theorem mapsTo_spliceArcFlip : MapsTo spliceArcFlip spliceArcPos spliceArcPos := by
  rintro p ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  rw [spliceArcFlip_apply]
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · change (-1 : ℝ) ≤ -p.2
    linarith [hsq.2.2]
  · change -p.2 ≤ (1 : ℝ)
    linarith [hsq.2.1]
  · change (-1 : ℝ) ≤ -p.1
    linarith [hsq.1.2]
  · change -p.1 ≤ (1 : ℝ)
    linarith [hsq.1.1]
  · change -p.2 - -p.1 = 1
    linarith

/-- The flip sends the endpoint `(1, 0)` of the chord `x - y = 1` to its other endpoint. -/
theorem spliceArcFlip_apply_right : spliceArcFlip ((1 : ℝ), (0 : ℝ)) = (0, -1) := by
  rw [spliceArcFlip_apply]
  norm_num

/-- The flip sends the endpoint `(0, -1)` of the chord `x - y = 1` to its other endpoint. -/
theorem spliceArcFlip_apply_left : spliceArcFlip ((0 : ℝ), (-1 : ℝ)) = (1, 0) := by
  rw [spliceArcFlip_apply]
  norm_num

/-- The endpoint `(1, 0)` lies on the chord `x - y = 1`. -/
theorem right_mem_spliceArcPos : ((1 : ℝ), (0 : ℝ)) ∈ spliceArcPos :=
  ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩

/-- The flip is not the identity on the chord `x - y = 1`, so it is a genuine alternative to
the return map computed below. -/
theorem exists_spliceArcFlip_ne_self : ∃ p ∈ spliceArcPos, spliceArcFlip p ≠ p := by
  refine ⟨((1 : ℝ), (0 : ℝ)), right_mem_spliceArcPos, ?_⟩
  rw [spliceArcFlip_apply_right]
  norm_num

/-- **Two periods return the chord `x - y = 1` to itself by the identity.** Running twice
around the branch circle composes the period map with itself, and the coordinate swap is an
involution, so the chord comes back without reversal. -/
theorem swap_comp_swap_eqOn_spliceArcPos :
    EqOn (Prod.swap ∘ Prod.swap) id spliceArcPos := fun p _ => Prod.swap_swap p

/-- **The two period return map is not the flip.** Together with
`swap_comp_swap_eqOn_spliceArcPos` this is the annulus side of the dichotomy: a Möbius band
would return each chord to itself by the endpoint exchanging flip. -/
theorem exists_swap_comp_swap_ne_spliceArcFlip :
    ∃ p ∈ spliceArcPos, (Prod.swap ∘ Prod.swap) p ≠ spliceArcFlip p := by
  obtain ⟨p, hp, hne⟩ := exists_spliceArcFlip_ne_self
  exact ⟨p, hp, fun h => hne (h.symm.trans (swap_comp_swap_eqOn_spliceArcPos hp))⟩

/-! ### The replacement matches the crossing configuration on the lateral boundary -/

/-- The replacement meets the lateral boundary of the square in the same set as the crossing
configuration, namely in the four points `spliceEnds`. -/
theorem spliceArc_inter_lateral_eq_crossingArc :
    (spliceArcPos ∪ spliceArcNeg) ∩ spliceSquareBoundary
      = (crossingArcX ∪ crossingArcY) ∩ spliceSquareBoundary := by
  rw [spliceArc_inter_spliceSquareBoundary, crossingArc_inter_spliceSquareBoundary]

/-- The match is only a match of the whole four point set: the chord `x - y = 1` joins an
endpoint of one crossing arc to an endpoint of the other, so the replacement re-pairs the four
lateral points instead of reproducing the vertical crossing arc. -/
theorem spliceArcPos_inter_lateral_ne_crossingArcX :
    spliceArcPos ∩ spliceSquareBoundary ≠ crossingArcX ∩ spliceSquareBoundary := by
  rw [spliceArcPos_inter_spliceSquareBoundary, crossingArcX_inter_spliceSquareBoundary]
  intro h
  have hmem : ((1 : ℝ), (0 : ℝ))
      ∈ ({((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} : Set (ℝ × ℝ)) := Or.inl rfl
  rw [h] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  norm_num at hmem

/-- The replacement does not reproduce the horizontal crossing arc either. -/
theorem spliceArcPos_inter_lateral_ne_crossingArcY :
    spliceArcPos ∩ spliceSquareBoundary ≠ crossingArcY ∩ spliceSquareBoundary := by
  rw [spliceArcPos_inter_spliceSquareBoundary, crossingArcY_inter_spliceSquareBoundary]
  intro h
  have hmem : ((0 : ℝ), (-1 : ℝ))
      ∈ ({((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} : Set (ℝ × ℝ)) := Or.inr rfl
  rw [h] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  norm_num at hmem

/-! ### Why the other pair of chords is the wrong replacement here -/

/-- The trace of the plane `x + y = 1` on the square, the chord used in the boundary arc
case. -/
def spliceSumArcPos : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 + p.2 = 1}

/-- The trace of the plane `x + y = -1` on the square. -/
def spliceSumArcNeg : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 + p.2 = -1}

/-- The period map carries the chord `x + y = 1` to itself. -/
theorem swap_mem_spliceSumArcPos {p : ℝ × ℝ} (hp : p ∈ spliceSumArcPos) :
    p.swap ∈ spliceSumArcPos :=
  ⟨swap_mem_spliceSquare hp.1, by
    have h := hp.2
    change p.2 + p.1 = 1
    linarith⟩

/-- **The other pair of chords is preserved, not exchanged.** Unlike `spliceArcPos`, the chord
`x + y = 1` is carried to itself by the period map, so it closes up after a single period. -/
theorem swap_image_spliceSumArcPos : Prod.swap '' spliceSumArcPos = spliceSumArcPos := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_spliceSumArcPos hq
  · intro p hp
    exact ⟨p.swap, swap_mem_spliceSumArcPos hp, Prod.swap_swap p⟩

/-- **The single period return on the other pair of chords is the flip.** The period map moves
the endpoint `(1, 0)` of `x + y = 1` to its other endpoint `(0, 1)`, so that chord would close
up into a Möbius band, which is why `x + y = ±1` cannot be the replacement in the closed
case. -/
theorem exists_swap_ne_self_mem_spliceSumArcPos : ∃ p ∈ spliceSumArcPos, p.swap ≠ p := by
  refine ⟨((1 : ℝ), (0 : ℝ)), ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩, ?_⟩
  norm_num

/-- The chord `x + y = 1` meets the lateral boundary in the two points `(1, 0)` and
`(0, 1)`. -/
theorem spliceSumArcPos_inter_spliceSquareBoundary :
    spliceSumArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exfalso; rw [h] at hd; linarith [hsq.2.2]
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exfalso; rw [h] at hd; linarith [hsq.1.2]
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

/-- The chord `x + y = -1` meets the lateral boundary in the two points `(-1, 0)` and
`(0, -1)`. -/
theorem spliceSumArcNeg_inter_spliceSquareBoundary :
    spliceSumArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exfalso; rw [h] at hd; linarith [hsq.2.1]
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
    · exfalso; rw [h] at hd; linarith [hsq.1.1]
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

/-- The other pair of chords has the same four lateral endpoints as the crossing
configuration, so the lateral match alone does not select the correct replacement. -/
theorem spliceSumArc_inter_spliceSquareBoundary :
    (spliceSumArcPos ∪ spliceSumArcNeg) ∩ spliceSquareBoundary = spliceEnds := by
  rw [Set.union_inter_distrib_right, spliceSumArcPos_inter_spliceSquareBoundary,
    spliceSumArcNeg_inter_spliceSquareBoundary]
  ext p
  simp only [spliceEnds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-! ### The two chord maps are conjugate by the period map -/

/-- Value of the first chord map on the vertical crossing arc. -/
theorem crossSeamChordPos_apply_crossingArcX (s : ℝ) :
    crossSeamChordPos ((0 : ℝ), s) = ((s + 1) / 2, (s - 1) / 2) := by
  refine Prod.ext ?_ ?_
  · change ((0 : ℝ) + s + 1) / 2 = (s + 1) / 2
    ring
  · change ((0 : ℝ) + s - 1) / 2 = (s - 1) / 2
    ring

/-- Value of the second chord map on the horizontal crossing arc. -/
theorem crossSeamChordNeg_apply_crossingArcY (s : ℝ) :
    crossSeamChordNeg (s, (0 : ℝ)) = ((s - 1) / 2, (s + 1) / 2) := by
  refine Prod.ext ?_ ?_
  · change (s + (0 : ℝ) - 1) / 2 = (s - 1) / 2
    ring
  · change (s + (0 : ℝ) + 1) / 2 = (s + 1) / 2
    ring

/-- **The two chord maps of the boundary case are conjugate by the period map.** This is why
the same two maps resolve the closed case: the period map exchanges the two chords and
intertwines the two resolutions. -/
theorem crossSeamChordNeg_eq_swap (p : ℝ × ℝ) :
    crossSeamChordNeg p = (crossSeamChordPos p.swap).swap := by
  refine Prod.ext ?_ ?_
  · change (p.1 + p.2 - 1) / 2 = (p.2 + p.1 - 1) / 2
    ring
  · change (p.1 + p.2 + 1) / 2 = (p.2 + p.1 + 1) / 2
    ring

/-- The two chord maps agree across one period on the crossing arcs. -/
theorem crossSeamChordNeg_apply_swap (s : ℝ) :
    crossSeamChordNeg (s, (0 : ℝ)) = (crossSeamChordPos ((0 : ℝ), s)).swap := by
  rw [crossSeamChordPos_apply_crossingArcX, crossSeamChordNeg_apply_crossingArcY]
  rfl

/-- The same agreement read in the other direction. -/
theorem crossSeamChordPos_apply_swap (s : ℝ) :
    crossSeamChordPos ((0 : ℝ), s) = (crossSeamChordNeg (s, (0 : ℝ))).swap := by
  rw [crossSeamChordPos_apply_crossingArcX, crossSeamChordNeg_apply_crossingArcY]
  rfl

/-- The first chord map carries the vertical crossing arc into the chord `x - y = 1`. -/
theorem crossSeamChordPos_mem_spliceArcPos {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    crossSeamChordPos ((0 : ℝ), s) ∈ spliceArcPos := by
  rw [crossSeamChordPos_apply_crossingArcX]
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · change (-1 : ℝ) ≤ (s + 1) / 2
    linarith
  · change (s + 1) / 2 ≤ (1 : ℝ)
    linarith
  · change (-1 : ℝ) ≤ (s - 1) / 2
    linarith
  · change (s - 1) / 2 ≤ (1 : ℝ)
    linarith
  · change (s + 1) / 2 - (s - 1) / 2 = 1
    ring

/-- The second chord map carries the horizontal crossing arc into the chord `x - y = -1`. -/
theorem crossSeamChordNeg_mem_spliceArcNeg {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1) :
    crossSeamChordNeg (s, (0 : ℝ)) ∈ spliceArcNeg := by
  rw [crossSeamChordNeg_apply_crossingArcY]
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · change (-1 : ℝ) ≤ (s - 1) / 2
    linarith
  · change (s - 1) / 2 ≤ (1 : ℝ)
    linarith
  · change (-1 : ℝ) ≤ (s + 1) / 2
    linarith
  · change (s + 1) / 2 ≤ (1 : ℝ)
    linarith
  · change (s - 1) / 2 - (s + 1) / 2 = -1
    ring

/-- The first chord map covers the whole chord `x - y = 1` from the vertical crossing arc. -/
theorem exists_crossSeamChordPos_eq_of_mem_spliceArcPos {a : ℝ × ℝ} (ha : a ∈ spliceArcPos) :
    ∃ s : ℝ, -1 ≤ s ∧ s ≤ 1 ∧ crossSeamChordPos ((0 : ℝ), s) = a := by
  obtain ⟨hsq, hd⟩ := ha
  rw [mem_spliceSquare] at hsq
  refine ⟨2 * a.1 - 1, by linarith [hsq.2.1], by linarith [hsq.1.2], ?_⟩
  rw [crossSeamChordPos_apply_crossingArcX]
  refine Prod.ext ?_ ?_
  · change (2 * a.1 - 1 + 1) / 2 = a.1
    ring
  · change (2 * a.1 - 1 - 1) / 2 = a.2
    linarith

/-- The second chord map covers the whole chord `x - y = -1` from the horizontal crossing
arc. -/
theorem exists_crossSeamChordNeg_eq_of_mem_spliceArcNeg {a : ℝ × ℝ} (ha : a ∈ spliceArcNeg) :
    ∃ s : ℝ, -1 ≤ s ∧ s ≤ 1 ∧ crossSeamChordNeg (s, (0 : ℝ)) = a := by
  obtain ⟨hsq, hd⟩ := ha
  rw [mem_spliceSquare] at hsq
  refine ⟨2 * a.2 - 1, by linarith [hsq.1.1], by linarith [hsq.2.2], ?_⟩
  rw [crossSeamChordNeg_apply_crossingArcY]
  refine Prod.ext ?_ ?_
  · change (2 * a.2 - 1 - 1) / 2 = a.1
    linarith
  · change (2 * a.2 - 1 + 1) / 2 = a.2
    ring

/-! ### The source annulus and the two maps of the model -/

/-- The closed rectangle of the model: the transverse parameter runs over `[-1, 1]` and the
base parameter over two periods `[0, 2]` of the branch circle. -/
def closedSeamRect : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 2

/-- The source annulus of the first closed branch case, presented as a fundamental domain: the
second period end is left out because it is the identified copy of the first. -/
def closedSeamSource : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 2

/-- Membership in the closed rectangle of the model. -/
theorem mem_closedSeamRect {p : ℝ × ℝ} :
    p ∈ closedSeamRect ↔ (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 2) := by
  simp only [closedSeamRect, Set.mem_prod, Set.mem_Icc]

/-- Membership in the source annulus. -/
theorem mem_closedSeamSource {p : ℝ × ℝ} :
    p ∈ closedSeamSource ↔ (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 < 2) := by
  simp only [closedSeamSource, Set.mem_prod, Set.mem_Icc, Set.mem_Ico]

/-- The fundamental domain sits inside the closed rectangle. -/
theorem closedSeamSource_subset_closedSeamRect : closedSeamSource ⊆ closedSeamRect := by
  rintro p ⟨h1, h2⟩
  exact ⟨h1, Set.Ico_subset_Icc_self h2⟩

/-- The closed rectangle of the model is a piecewise linear disk. -/
theorem isPLBall_closedSeamRect : IsPLBall 2 closedSeamRect := by
  rw [closedSeamRect]
  exact isPLBall_two_prod (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))
    (isPLBall_Icc (by norm_num : (0 : ℝ) < 2))

/-- The old crossing configuration swept around the branch circle, read on the source annulus:
the first period covers the sheet `x = 0` of the tube and the second the sheet `y = 0`. -/
noncomputable def closedSeamInclude (p : ℝ × ℝ) : Quotient spliceSetoid :=
  if p.2 ≤ 1 then spliceMk (((0 : ℝ), p.1), p.2) else spliceMk ((p.1, (0 : ℝ)), p.2 - 1)

/-- Moise's replacement swept around the branch circle, read on the same source annulus: the
first period covers the chord `x - y = 1` of the tube and the second the chord `x - y = -1`,
the period map exchanging the two. -/
noncomputable def closedSeamResolve (p : ℝ × ℝ) : Quotient spliceSetoid :=
  if p.2 ≤ 1 then spliceMk (crossSeamChordPos ((0 : ℝ), p.1), p.2)
  else spliceMk (crossSeamChordNeg (p.1, (0 : ℝ)), p.2 - 1)

/-- The crossing map on the first period. -/
theorem closedSeamInclude_of_le_one {p : ℝ × ℝ} (h : p.2 ≤ 1) :
    closedSeamInclude p = spliceMk (((0 : ℝ), p.1), p.2) := by
  rw [closedSeamInclude, if_pos h]

/-- The crossing map on the second period. The two descriptions agree at the seam because the
period identification glues the top of the sheet `x = 0` to the bottom of the sheet
`y = 0`. -/
theorem closedSeamInclude_of_one_le {p : ℝ × ℝ} (h : 1 ≤ p.2) :
    closedSeamInclude p = spliceMk ((p.1, (0 : ℝ)), p.2 - 1) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [closedSeamInclude, if_neg (not_le.mpr hlt)]
  · rw [closedSeamInclude, if_pos (le_of_eq heq.symm)]
    refine spliceMk_eq_iff.mpr (Or.inr (Or.inr ⟨heq.symm, ?_, rfl⟩))
    rw [← heq]
    norm_num

/-- The replacement map on the first period. -/
theorem closedSeamResolve_of_le_one {p : ℝ × ℝ} (h : p.2 ≤ 1) :
    closedSeamResolve p = spliceMk (crossSeamChordPos ((0 : ℝ), p.1), p.2) := by
  rw [closedSeamResolve, if_pos h]

/-- The replacement map on the second period. The two descriptions agree at the seam because
the period map exchanges the two chords. -/
theorem closedSeamResolve_of_one_le {p : ℝ × ℝ} (h : 1 ≤ p.2) :
    closedSeamResolve p = spliceMk (crossSeamChordNeg (p.1, (0 : ℝ)), p.2 - 1) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [closedSeamResolve, if_neg (not_le.mpr hlt)]
  · rw [closedSeamResolve, if_pos (le_of_eq heq.symm)]
    refine spliceMk_eq_iff.mpr (Or.inr (Or.inr ⟨heq.symm, ?_, ?_⟩))
    · rw [← heq]
      norm_num
    · exact crossSeamChordPos_apply_swap p.1

/-! ### The crossing configuration keeps the branch -/

/-- Two distinct source points with the same image under the crossing map lie over the core of
the tube, and their common image is a point of the core circle. -/
theorem exists_core_of_closedSeamInclude_eq {p q : ℝ × ℝ} (hp : p ∈ closedSeamSource)
    (hq : q ∈ closedSeamSource) (hne : p ≠ q)
    (h : closedSeamInclude p = closedSeamInclude q) :
    ∃ t ∈ Ico (0 : ℝ) 1, closedSeamInclude p = spliceMk (((0 : ℝ), (0 : ℝ)), t) := by
  rw [mem_closedSeamSource] at hp hq
  by_cases hp1 : p.2 < 1 <;> by_cases hq1 : q.2 < 1
  · rw [closedSeamInclude_of_le_one (le_of_lt hp1),
      closedSeamInclude_of_le_one (le_of_lt hq1)] at h
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((0 : ℝ), p.1), p.2))
      (q := (((0 : ℝ), q.1), q.2)) (ne_of_lt hp1) (ne_of_lt hq1) h
    have hf := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    have hfs := congrArg Prod.snd hf
    exact absurd (Prod.ext hfs hs) hne
  · have hq1' : 1 ≤ q.2 := not_lt.mp hq1
    rw [closedSeamInclude_of_le_one (le_of_lt hp1), closedSeamInclude_of_one_le hq1'] at h
    have hq2 : q.2 - 1 ≠ 1 := by
      intro hc
      linarith [hq.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((0 : ℝ), p.1), p.2))
      (q := ((q.1, (0 : ℝ)), q.2 - 1)) (ne_of_lt hp1) hq2 h
    have hf := congrArg Prod.fst he
    have hfs := congrArg Prod.snd hf
    have h1 : p.1 = 0 := hfs
    refine ⟨p.2, Set.mem_Ico.mpr ⟨hp.2.1, hp1⟩, ?_⟩
    rw [closedSeamInclude_of_le_one (le_of_lt hp1), h1]
  · have hp1' : 1 ≤ p.2 := not_lt.mp hp1
    rw [closedSeamInclude_of_one_le hp1', closedSeamInclude_of_le_one (le_of_lt hq1)] at h
    have hp2 : p.2 - 1 ≠ 1 := by
      intro hc
      linarith [hp.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := ((p.1, (0 : ℝ)), p.2 - 1))
      (q := (((0 : ℝ), q.1), q.2)) hp2 (ne_of_lt hq1) h
    have hf := congrArg Prod.fst he
    have hff := congrArg Prod.fst hf
    have h1 : p.1 = 0 := hff
    refine ⟨p.2 - 1, Set.mem_Ico.mpr ⟨by linarith, by linarith [hp.2.2]⟩, ?_⟩
    rw [closedSeamInclude_of_one_le hp1', h1]
  · have hp1' : 1 ≤ p.2 := not_lt.mp hp1
    have hq1' : 1 ≤ q.2 := not_lt.mp hq1
    rw [closedSeamInclude_of_one_le hp1', closedSeamInclude_of_one_le hq1'] at h
    have hp2 : p.2 - 1 ≠ 1 := by
      intro hc
      linarith [hp.2.2]
    have hq2 : q.2 - 1 ≠ 1 := by
      intro hc
      linarith [hq.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := ((p.1, (0 : ℝ)), p.2 - 1))
      (q := ((q.1, (0 : ℝ)), q.2 - 1)) hp2 hq2 h
    have hf := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    have hff := congrArg Prod.fst hf
    have h1 : p.1 = q.1 := hff
    have h2 : p.2 - 1 = q.2 - 1 := hs
    exact absurd (Prod.ext h1 (by linarith)) hne

/-- **The crossing configuration keeps the branch.** Swept around the branch circle its double
point set is the whole core circle, at every level of the tube. -/
theorem doublePointSet_closedSeamInclude :
    doublePointSet closedSeamInclude closedSeamSource = spliceMk '' spliceCore := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, q, hq, hne, hpy, hqy⟩
    obtain ⟨t, ht, hpt⟩ := exists_core_of_closedSeamInclude_eq hp hq hne (hpy.trans hqy.symm)
    rw [image_spliceCore_eq_image_Ico]
    exact ⟨(((0 : ℝ), (0 : ℝ)), t), ⟨rfl, ht⟩, hpt.symm.trans hpy⟩
  · rw [image_spliceCore_eq_image_Ico]
    rintro y ⟨z, ⟨hz1, hz2⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hz1
    rw [Set.mem_Ico] at hz2
    have hz : z = (((0 : ℝ), (0 : ℝ)), z.2) := Prod.ext hz1 rfl
    refine ⟨((0 : ℝ), z.2), ?_, ((0 : ℝ), z.2 + 1), ?_, ?_, ?_, ?_⟩
    · exact mem_closedSeamSource.mpr ⟨⟨by norm_num, by norm_num⟩, hz2.1, by linarith [hz2.2]⟩
    · exact mem_closedSeamSource.mpr
        ⟨⟨by norm_num, by norm_num⟩, by linarith [hz2.1], by linarith [hz2.2]⟩
    · intro hcon
      have hc : z.2 = z.2 + 1 := congrArg Prod.snd hcon
      linarith
    · have h1 : closedSeamInclude (((0 : ℝ), z.2) : ℝ × ℝ)
          = spliceMk (((0 : ℝ), (0 : ℝ)), z.2) := closedSeamInclude_of_le_one (le_of_lt hz2.2)
      rw [h1]
      exact congrArg spliceMk hz.symm
    · have h1 : closedSeamInclude (((0 : ℝ), z.2 + 1) : ℝ × ℝ)
          = spliceMk (((0 : ℝ), (0 : ℝ)), z.2 + 1 - 1) :=
        closedSeamInclude_of_one_le (by linarith [hz2.1])
      have h2 : z.2 + 1 - 1 = z.2 := by ring
      rw [h1, h2]
      exact congrArg spliceMk hz.symm

/-! ### The replacement deletes the branch -/

/-- **The replacement is injective on the source annulus.** The two chords are disjoint, and
the period identification cannot bring a point of the first period onto a point of the second
inside the fundamental domain. -/
theorem injOn_closedSeamResolve : InjOn closedSeamResolve closedSeamSource := by
  intro p hp q hq h
  rw [mem_closedSeamSource] at hp hq
  by_cases hp1 : p.2 < 1 <;> by_cases hq1 : q.2 < 1
  · have hP : closedSeamResolve p = spliceMk (((p.1 + 1) / 2, (p.1 - 1) / 2), p.2) := by
      rw [closedSeamResolve_of_le_one (le_of_lt hp1), crossSeamChordPos_apply_crossingArcX]
    have hQ : closedSeamResolve q = spliceMk (((q.1 + 1) / 2, (q.1 - 1) / 2), q.2) := by
      rw [closedSeamResolve_of_le_one (le_of_lt hq1), crossSeamChordPos_apply_crossingArcX]
    rw [hP, hQ] at h
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((p.1 + 1) / 2, (p.1 - 1) / 2), p.2))
      (q := (((q.1 + 1) / 2, (q.1 - 1) / 2), q.2)) (ne_of_lt hp1) (ne_of_lt hq1) h
    have hf := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    have hff := congrArg Prod.fst hf
    have h1 : (p.1 + 1) / 2 = (q.1 + 1) / 2 := hff
    exact Prod.ext (by linarith) hs
  · have hq1' : 1 ≤ q.2 := not_lt.mp hq1
    have hP : closedSeamResolve p = spliceMk (((p.1 + 1) / 2, (p.1 - 1) / 2), p.2) := by
      rw [closedSeamResolve_of_le_one (le_of_lt hp1), crossSeamChordPos_apply_crossingArcX]
    have hQ : closedSeamResolve q = spliceMk (((q.1 - 1) / 2, (q.1 + 1) / 2), q.2 - 1) := by
      rw [closedSeamResolve_of_one_le hq1', crossSeamChordNeg_apply_crossingArcY]
    rw [hP, hQ] at h
    have hq2 : q.2 - 1 ≠ 1 := by
      intro hc
      linarith [hq.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((p.1 + 1) / 2, (p.1 - 1) / 2), p.2))
      (q := (((q.1 - 1) / 2, (q.1 + 1) / 2), q.2 - 1)) (ne_of_lt hp1) hq2 h
    have hf := congrArg Prod.fst he
    have hff := congrArg Prod.fst hf
    have hfs := congrArg Prod.snd hf
    have h1 : (p.1 + 1) / 2 = (q.1 - 1) / 2 := hff
    have h2 : (p.1 - 1) / 2 = (q.1 + 1) / 2 := hfs
    exfalso
    linarith
  · have hp1' : 1 ≤ p.2 := not_lt.mp hp1
    have hP : closedSeamResolve p = spliceMk (((p.1 - 1) / 2, (p.1 + 1) / 2), p.2 - 1) := by
      rw [closedSeamResolve_of_one_le hp1', crossSeamChordNeg_apply_crossingArcY]
    have hQ : closedSeamResolve q = spliceMk (((q.1 + 1) / 2, (q.1 - 1) / 2), q.2) := by
      rw [closedSeamResolve_of_le_one (le_of_lt hq1), crossSeamChordPos_apply_crossingArcX]
    rw [hP, hQ] at h
    have hp2 : p.2 - 1 ≠ 1 := by
      intro hc
      linarith [hp.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((p.1 - 1) / 2, (p.1 + 1) / 2), p.2 - 1))
      (q := (((q.1 + 1) / 2, (q.1 - 1) / 2), q.2)) hp2 (ne_of_lt hq1) h
    have hf := congrArg Prod.fst he
    have hff := congrArg Prod.fst hf
    have hfs := congrArg Prod.snd hf
    have h1 : (p.1 - 1) / 2 = (q.1 + 1) / 2 := hff
    have h2 : (p.1 + 1) / 2 = (q.1 - 1) / 2 := hfs
    exfalso
    linarith
  · have hp1' : 1 ≤ p.2 := not_lt.mp hp1
    have hq1' : 1 ≤ q.2 := not_lt.mp hq1
    have hP : closedSeamResolve p = spliceMk (((p.1 - 1) / 2, (p.1 + 1) / 2), p.2 - 1) := by
      rw [closedSeamResolve_of_one_le hp1', crossSeamChordNeg_apply_crossingArcY]
    have hQ : closedSeamResolve q = spliceMk (((q.1 - 1) / 2, (q.1 + 1) / 2), q.2 - 1) := by
      rw [closedSeamResolve_of_one_le hq1', crossSeamChordNeg_apply_crossingArcY]
    rw [hP, hQ] at h
    have hp2 : p.2 - 1 ≠ 1 := by
      intro hc
      linarith [hp.2.2]
    have hq2 : q.2 - 1 ≠ 1 := by
      intro hc
      linarith [hq.2.2]
    have he := eq_of_spliceMk_eq_of_snd_ne_one (p := (((p.1 - 1) / 2, (p.1 + 1) / 2), p.2 - 1))
      (q := (((q.1 - 1) / 2, (q.1 + 1) / 2), q.2 - 1)) hp2 hq2 h
    have hf := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    have hff := congrArg Prod.fst hf
    have h1 : (p.1 - 1) / 2 = (q.1 - 1) / 2 := hff
    have h2 : p.2 - 1 = q.2 - 1 := hs
    exact Prod.ext (by linarith) (by linarith)

/-- **The replacement deletes the branch and creates no other double point.** Swept around the
branch circle it has no double point at all, whereas the crossing configuration had the whole
core circle. -/
theorem doublePointSet_closedSeamResolve :
    doublePointSet closedSeamResolve closedSeamSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn closedSeamResolve closedSeamSource).mpr
    injOn_closedSeamResolve

/-! ### Both maps cover their figures -/

/-- The crossing map covers exactly the image of the crossing configuration in the spliced
cylinder. -/
theorem image_closedSeamInclude :
    closedSeamInclude '' closedSeamSource = spliceMk '' crossingFigure := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    rw [mem_closedSeamSource] at hp
    by_cases h1 : p.2 ≤ 1
    · refine ⟨(((0 : ℝ), p.1), p.2), ⟨Or.inl ⟨?_, rfl⟩, Set.mem_Icc.mpr ⟨hp.2.1, h1⟩⟩, ?_⟩
      · exact mem_spliceSquare.mpr ⟨⟨by norm_num, by norm_num⟩, hp.1⟩
      · exact (closedSeamInclude_of_le_one h1).symm
    · have h1' : 1 < p.2 := not_le.mp h1
      refine ⟨((p.1, (0 : ℝ)), p.2 - 1),
        ⟨Or.inr ⟨?_, rfl⟩, Set.mem_Icc.mpr ⟨by linarith, by linarith [hp.2.2]⟩⟩, ?_⟩
      · exact mem_spliceSquare.mpr ⟨hp.1, by norm_num, by norm_num⟩
      · exact (closedSeamInclude_of_one_le (le_of_lt h1')).symm
  · rintro y ⟨z, ⟨hz1, hz2⟩, rfl⟩
    rw [Set.mem_Icc] at hz2
    rcases hz1 with ha | ha
    · have hsq := mem_spliceSquare.mp ha.1
      refine ⟨(z.1.2, z.2), mem_closedSeamSource.mpr ⟨hsq.2, hz2.1, by linarith [hz2.2]⟩, ?_⟩
      have h1 : closedSeamInclude ((z.1.2, z.2) : ℝ × ℝ)
          = spliceMk (((0 : ℝ), z.1.2), z.2) := closedSeamInclude_of_le_one hz2.2
      rw [h1]
      exact congrArg spliceMk (Prod.ext (Prod.ext ha.2.symm rfl) rfl)
    · have hsq := mem_spliceSquare.mp ha.1
      have hzz : ((z.1.1, (0 : ℝ)), z.2) = z := Prod.ext (Prod.ext rfl ha.2.symm) rfl
      rcases lt_or_eq_of_le hz2.2 with hlt | heq
      · refine ⟨(z.1.1, z.2 + 1),
          mem_closedSeamSource.mpr ⟨hsq.1, by linarith [hz2.1], by linarith⟩, ?_⟩
        have h1 : closedSeamInclude ((z.1.1, z.2 + 1) : ℝ × ℝ)
            = spliceMk ((z.1.1, (0 : ℝ)), z.2 + 1 - 1) :=
          closedSeamInclude_of_one_le (by linarith [hz2.1])
        have h2 : z.2 + 1 - 1 = z.2 := by ring
        rw [h1, h2, hzz]
      · refine ⟨(z.1.1, (0 : ℝ)),
          mem_closedSeamSource.mpr ⟨hsq.1, le_rfl, by norm_num⟩, ?_⟩
        have h1 : closedSeamInclude ((z.1.1, (0 : ℝ)) : ℝ × ℝ)
            = spliceMk (((0 : ℝ), z.1.1), (0 : ℝ)) :=
          closedSeamInclude_of_le_one zero_le_one
        rw [h1]
        exact spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, heq, Prod.ext rfl ha.2⟩))

/-- The replacement map covers exactly the image of the replacement figure in the spliced
cylinder, so the vanishing of its double point set is not an artefact of a small image. -/
theorem image_closedSeamResolve :
    closedSeamResolve '' closedSeamSource = spliceMk '' spliceFigure := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    rw [mem_closedSeamSource] at hp
    by_cases h1 : p.2 ≤ 1
    · refine ⟨(crossSeamChordPos ((0 : ℝ), p.1), p.2),
        ⟨Or.inl (crossSeamChordPos_mem_spliceArcPos hp.1.1 hp.1.2),
          Set.mem_Icc.mpr ⟨hp.2.1, h1⟩⟩, ?_⟩
      exact (closedSeamResolve_of_le_one h1).symm
    · have h1' : 1 < p.2 := not_le.mp h1
      refine ⟨(crossSeamChordNeg (p.1, (0 : ℝ)), p.2 - 1),
        ⟨Or.inr (crossSeamChordNeg_mem_spliceArcNeg hp.1.1 hp.1.2),
          Set.mem_Icc.mpr ⟨by linarith, by linarith [hp.2.2]⟩⟩, ?_⟩
      exact (closedSeamResolve_of_one_le (le_of_lt h1')).symm
  · rintro y ⟨z, ⟨hz1, hz2⟩, rfl⟩
    rw [Set.mem_Icc] at hz2
    rcases hz1 with ha | ha
    · obtain ⟨s, hs, hs', hsa⟩ := exists_crossSeamChordPos_eq_of_mem_spliceArcPos ha
      refine ⟨(s, z.2), mem_closedSeamSource.mpr ⟨⟨hs, hs'⟩, hz2.1, by linarith [hz2.2]⟩, ?_⟩
      have h1 : closedSeamResolve ((s, z.2) : ℝ × ℝ)
          = spliceMk (crossSeamChordPos ((0 : ℝ), s), z.2) :=
        closedSeamResolve_of_le_one hz2.2
      rw [h1, hsa]
    · obtain ⟨s, hs, hs', hsa⟩ := exists_crossSeamChordNeg_eq_of_mem_spliceArcNeg ha
      rcases lt_or_eq_of_le hz2.2 with hlt | heq
      · refine ⟨(s, z.2 + 1),
          mem_closedSeamSource.mpr ⟨⟨hs, hs'⟩, by linarith [hz2.1], by linarith⟩, ?_⟩
        have h1 : closedSeamResolve ((s, z.2 + 1) : ℝ × ℝ)
            = spliceMk (crossSeamChordNeg (s, (0 : ℝ)), z.2 + 1 - 1) :=
          closedSeamResolve_of_one_le (by linarith [hz2.1])
        have h2 : z.2 + 1 - 1 = z.2 := by ring
        rw [h1, h2, hsa]
      · refine ⟨(s, (0 : ℝ)),
          mem_closedSeamSource.mpr ⟨⟨hs, hs'⟩, le_rfl, by norm_num⟩, ?_⟩
        have h1 : closedSeamResolve ((s, (0 : ℝ)) : ℝ × ℝ)
            = spliceMk (crossSeamChordPos ((0 : ℝ), s), (0 : ℝ)) :=
          closedSeamResolve_of_le_one zero_le_one
        rw [h1]
        exact spliceMk_eq_iff.mpr
          (Or.inr (Or.inl ⟨rfl, heq, hsa.symm.trans (crossSeamChordNeg_apply_swap s)⟩))

/-! ### The replacement is an annulus and not a Möbius band -/

/-- **The band closes up without a twist.** Two periods bring the transverse parameter `s`
back to itself, not to `-s`, which is the untwisted gluing of the rectangle. -/
theorem closedSeamResolve_bottom_eq_top (s : ℝ) :
    closedSeamResolve (s, (0 : ℝ)) = closedSeamResolve (s, (2 : ℝ)) := by
  have h0 : closedSeamResolve ((s, (0 : ℝ)) : ℝ × ℝ)
      = spliceMk (crossSeamChordPos ((0 : ℝ), s), (0 : ℝ)) :=
    closedSeamResolve_of_le_one zero_le_one
  have h2 : closedSeamResolve ((s, (2 : ℝ)) : ℝ × ℝ)
      = spliceMk (crossSeamChordNeg (s, (0 : ℝ)), (2 : ℝ) - 1) :=
    closedSeamResolve_of_one_le (by norm_num)
  rw [h0, h2]
  exact spliceMk_eq_iff.mpr
    (Or.inr (Or.inl ⟨rfl, by norm_num, crossSeamChordNeg_apply_swap s⟩))

/-- **The replacement identifies exactly the untwisted pairs.** On the closed rectangle of the
model the only identifications are between `(s, 0)` and `(s, 2)` with the same transverse
parameter, so the image of the replacement figure is the annulus quotient of the rectangle and
not its Möbius quotient. -/
theorem closedSeamResolve_eq_iff {p q : ℝ × ℝ} (hp : p ∈ closedSeamRect)
    (hq : q ∈ closedSeamRect) :
    closedSeamResolve p = closedSeamResolve q ↔
      p = q ∨ (p.2 = 0 ∧ q.2 = 2 ∧ p.1 = q.1) ∨ (p.2 = 2 ∧ q.2 = 0 ∧ p.1 = q.1) := by
  rw [mem_closedSeamRect] at hp hq
  constructor
  · intro h
    rcases eq_or_lt_of_le hp.2.2 with hp2 | hp2 <;> rcases eq_or_lt_of_le hq.2.2 with hq2 | hq2
    · have hp' : p = (p.1, (2 : ℝ)) := Prod.ext rfl hp2
      have hq' : q = (q.1, (2 : ℝ)) := Prod.ext rfl hq2
      have hpm : ((p.1, (0 : ℝ)) : ℝ × ℝ) ∈ closedSeamSource :=
        mem_closedSeamSource.mpr ⟨hp.1, le_rfl, by norm_num⟩
      have hqm : ((q.1, (0 : ℝ)) : ℝ × ℝ) ∈ closedSeamSource :=
        mem_closedSeamSource.mpr ⟨hq.1, le_rfl, by norm_num⟩
      have h' : closedSeamResolve ((p.1, (0 : ℝ)) : ℝ × ℝ)
          = closedSeamResolve ((q.1, (0 : ℝ)) : ℝ × ℝ) := by
        rw [closedSeamResolve_bottom_eq_top p.1, closedSeamResolve_bottom_eq_top q.1,
          ← hp', ← hq']
        exact h
      have hmem := injOn_closedSeamResolve hpm hqm h'
      have hf := congrArg Prod.fst hmem
      have h1 : p.1 = q.1 := hf
      exact Or.inl (Prod.ext h1 (hp2.trans hq2.symm))
    · have hp' : p = (p.1, (2 : ℝ)) := Prod.ext rfl hp2
      have hpm : ((p.1, (0 : ℝ)) : ℝ × ℝ) ∈ closedSeamSource :=
        mem_closedSeamSource.mpr ⟨hp.1, le_rfl, by norm_num⟩
      have hqm : q ∈ closedSeamSource := mem_closedSeamSource.mpr ⟨hq.1, hq.2.1, hq2⟩
      have h' : closedSeamResolve ((p.1, (0 : ℝ)) : ℝ × ℝ) = closedSeamResolve q := by
        rw [closedSeamResolve_bottom_eq_top p.1, ← hp']
        exact h
      have hmem := injOn_closedSeamResolve hpm hqm h'
      have hf := congrArg Prod.fst hmem
      have hs := congrArg Prod.snd hmem
      have h1 : p.1 = q.1 := hf
      have h2 : (0 : ℝ) = q.2 := hs
      exact Or.inr (Or.inr ⟨hp2, h2.symm, h1⟩)
    · have hq' : q = (q.1, (2 : ℝ)) := Prod.ext rfl hq2
      have hpm : p ∈ closedSeamSource := mem_closedSeamSource.mpr ⟨hp.1, hp.2.1, hp2⟩
      have hqm : ((q.1, (0 : ℝ)) : ℝ × ℝ) ∈ closedSeamSource :=
        mem_closedSeamSource.mpr ⟨hq.1, le_rfl, by norm_num⟩
      have h' : closedSeamResolve p = closedSeamResolve ((q.1, (0 : ℝ)) : ℝ × ℝ) := by
        rw [closedSeamResolve_bottom_eq_top q.1, ← hq']
        exact h
      have hmem := injOn_closedSeamResolve hpm hqm h'
      have hf := congrArg Prod.fst hmem
      have hs := congrArg Prod.snd hmem
      have h1 : p.1 = q.1 := hf
      have h2 : p.2 = 0 := hs
      exact Or.inr (Or.inl ⟨h2, hq2, h1⟩)
    · have hpm : p ∈ closedSeamSource := mem_closedSeamSource.mpr ⟨hp.1, hp.2.1, hp2⟩
      have hqm : q ∈ closedSeamSource := mem_closedSeamSource.mpr ⟨hq.1, hq.2.1, hq2⟩
      exact Or.inl (injOn_closedSeamResolve hpm hqm h)
  · rintro (rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · rfl
    · have hp' : p = (p.1, (0 : ℝ)) := Prod.ext rfl h1
      have hq' : q = (p.1, (2 : ℝ)) := Prod.ext h3.symm h2
      have hbt := closedSeamResolve_bottom_eq_top p.1
      rw [← hp', ← hq'] at hbt
      exact hbt
    · have hp' : p = (p.1, (2 : ℝ)) := Prod.ext rfl h1
      have hq' : q = (p.1, (0 : ℝ)) := Prod.ext h3.symm h2
      have hbt := closedSeamResolve_bottom_eq_top p.1
      rw [← hp', ← hq'] at hbt
      exact hbt.symm

/-- **The twisted gluing fails.** The Möbius identification of the rectangle, which would send
`(s, 2)` to `(-s, 0)`, is not induced by the replacement except at the fixed point `s = 0`. -/
theorem closedSeamResolve_top_ne_reflected_bottom {s : ℝ} (hs : -1 ≤ s) (hs' : s ≤ 1)
    (hs0 : s ≠ 0) : closedSeamResolve (s, (2 : ℝ)) ≠ closedSeamResolve (-s, (0 : ℝ)) := by
  intro h
  have hp : ((s, (2 : ℝ)) : ℝ × ℝ) ∈ closedSeamRect :=
    mem_closedSeamRect.mpr ⟨⟨hs, hs'⟩, by norm_num, le_rfl⟩
  have hq : ((-s, (0 : ℝ)) : ℝ × ℝ) ∈ closedSeamRect :=
    mem_closedSeamRect.mpr ⟨⟨by linarith, by linarith⟩, le_rfl, by norm_num⟩
  rcases (closedSeamResolve_eq_iff hp hq).mp h with h' | ⟨h1, -, -⟩ | ⟨-, -, h3⟩
  · have hc : (2 : ℝ) = 0 := congrArg Prod.snd h'
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := h1
    norm_num at hc
  · have hc : s = -s := h3
    exact hs0 (by linarith)

/-! ### Non-degeneracy of the model -/

/-- The source annulus is not empty. -/
theorem closedSeamSource_nonempty : closedSeamSource.Nonempty :=
  ⟨((0 : ℝ), (0 : ℝ)), mem_closedSeamSource.mpr ⟨by norm_num, by norm_num⟩⟩

/-- The branch that the replacement deletes is really there: the crossing configuration has a
nonempty double point set. -/
theorem doublePointSet_closedSeamInclude_nonempty :
    (doublePointSet closedSeamInclude closedSeamSource).Nonempty := by
  rw [doublePointSet_closedSeamInclude]
  exact spliceCore_nonempty.image spliceMk

/-- The two double point sets are different, so the deletion is not vacuous. -/
theorem doublePointSet_closedSeamInclude_ne_closedSeamResolve :
    doublePointSet closedSeamInclude closedSeamSource
      ≠ doublePointSet closedSeamResolve closedSeamSource := by
  rw [doublePointSet_closedSeamResolve]
  exact doublePointSet_closedSeamInclude_nonempty.ne_empty

/-- The core point of the spliced cylinder is not on the replacement figure: the chords miss
the centre of the square, and the period identification cannot bring them back to it. -/
theorem spliceMk_core_notMem_image_spliceFigure :
    spliceMk (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ∉ spliceMk '' spliceFigure := by
  rintro ⟨z, ⟨hz1, -⟩, hz⟩
  have hcentre : z.1 = ((0 : ℝ), (0 : ℝ)) := by
    rcases spliceMk_eq_iff.mp hz with h' | ⟨-, h1, -⟩ | ⟨-, -, h3⟩
    · exact congrArg Prod.fst h'
    · exfalso
      have hc : (0 : ℝ) = 1 := h1
      norm_num at hc
    · exact h3
  rcases hz1 with ha | ha
  · have hd : z.1.1 - z.1.2 = 1 := ha.2
    rw [hcentre] at hd
    norm_num at hd
  · have hd : z.1.1 - z.1.2 = -1 := ha.2
    rw [hcentre] at hd
    norm_num at hd

/-- The replacement really changes the figure inside the tube: the core point of the crossing
configuration is not on the replacement figure. -/
theorem image_spliceFigure_ne_image_crossingFigure :
    spliceMk '' spliceFigure ≠ spliceMk '' crossingFigure := by
  intro h
  refine spliceMk_core_notMem_image_spliceFigure ?_
  rw [h]
  exact ⟨(((0 : ℝ), (0 : ℝ)), (0 : ℝ)),
    ⟨Or.inl ⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
      Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩⟩, rfl⟩

/-- The replacement figure is not empty either, so the injectivity of `closedSeamResolve` is
injectivity of a map onto a genuine band. -/
theorem image_closedSeamResolve_nonempty :
    (closedSeamResolve '' closedSeamSource).Nonempty :=
  closedSeamSource_nonempty.image closedSeamResolve

end DifferentialGeometry.Topology.PiecewiseLinear
