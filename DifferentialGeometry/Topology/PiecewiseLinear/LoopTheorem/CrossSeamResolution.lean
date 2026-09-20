/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

/-!
# Resolving the two new seams of the boundary cross reglue

Moise's boundary arc case cuts the source disk along the two disjoint crosscuts that form the
preimage of a boundary branch and reglues the three resulting disks crosswise. The reglued map
pairs the four transverse half sheets correctly, but it still sends both new seams to the
centre of the transverse cross, so the branch survives: this is exactly the conclusion
`hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain` of
`exists_cross_reglued_cell_of_boundaryBranch`.

The repair replaces the two *bent* transverse arcs of the reglued map by the two *disjoint*
chords of the cross section square, fiberwise along the branch. This file builds that
replacement in the model of `DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice`,
whose square `spliceSquare`, transverse chords `spliceArcPos`, `spliceArcNeg` and cylinder
`spliceSquare ×ˢ Icc 0 1` are reused verbatim. The base here is the interval `Icc 0 1` and
*not* a circle, so no period identification and no sheet exchange occur: the resolution is a
genuine product along the base, which is the formal reason that the closed branch monodromy
obstruction is absent in the boundary arc case.

* `bentArcPos` and `bentArcNeg` are the two bent transverse arcs `[e₁, 0] ∪ [0, -e₂]` and
  `[-e₁, 0] ∪ [0, e₂]` of the raw cross reglue. They cover the old transverse cross
  (`bentArcPos_union_bentArcNeg`) and meet at the centre (`bentArcPos_inter_bentArcNeg`), so
  the corresponding sheets meet along the whole core curve (`bentSheetPos_inter_bentSheetNeg`)
  and the old figure is unchanged (`bentFigure_eq_crossingFigure`).
* `crossSeamChordPos` and `crossSeamChordNeg` are the resolutions. Each is the restriction of
  a single affine map of the plane, and each is a piecewise linear homeomorphism from a bent
  arc onto the corresponding chord (`isPLHomeomorphOn_crossSeamChordPos`,
  `isPLHomeomorphOn_crossSeamChordNeg`).
* `crossSeamResolvePos` and `crossSeamResolveNeg` are the fiberwise extensions along the base
  interval; they are piecewise linear homeomorphisms of the sheets
  (`isPLHomeomorphOn_crossSeamResolvePos`, `isPLHomeomorphOn_crossSeamResolveNeg`) and they do
  not move the base coordinate (`crossSeamResolvePos_snd`).
* Both the bent arcs and the chords are piecewise linear arcs (`isPLBall_bentArcPos`,
  `isPLBall_spliceArcPos`) and all four sheets are piecewise linear disks
  (`isPLBall_bentSheetPos`, `isPLBall_spliceSheetPos`).
* The replacement is the identity on the four lateral attaching intervals
  (`crossSeamResolvePos_eqOn_lateral`, `crossSeamResolveNeg_eqOn_lateral`) and it is supported
  in the cross section disks (`segment_crossSeamResolvePos_subset`), so at the two ends of the
  tube the boundary curves move inside the end disks only.
* `doublePointSet_crossSeamInclude` and `doublePointSet_crossSeamResolve` are the exact form of
  the deletion: inside the tube the raw cross reglue has the whole core curve as its double
  point set, and the resolved map has none, while `image_crossSeamResolve` records that the
  resolved image is the replacement figure and not a subset of the old one.

The counting consequence is isolated in `complexity_lt_of_branchEquiv_compl`: an equivalence
between the branches of the resolved triangulation and the old branches other than `c` gives
the strict complexity descent that Moise's induction consumes. A strict inclusion of singular
sets would not, since a subset of an arc can split into two arcs.

`CrossSeamResolutionData` records the full contract that a geometric producer of the resolved
cell has to supply, and the consumers below are proved from it. Not proved here: the existence
of a normal crossing product tube around a boundary branch, and therefore the production of
`CrossSeamResolutionData` itself from
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-! ### The four half sheets of the transverse cross -/

/-- A one point set of the line is an H-polytope. -/
theorem isHPolytope_singleton_real (a : ℝ) : IsHPolytope ({a} : Set ℝ) := by
  rw [← Set.Icc_self a]
  exact isHPolytope_Icc

/-- The half sheet `e₁` of the transverse cross: the positive part of the axis `y = 0`. -/
def crossRayPosX : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

/-- The half sheet `-e₁` of the transverse cross: the negative part of the axis `y = 0`. -/
def crossRayNegX : Set (ℝ × ℝ) := Icc (-1 : ℝ) 0 ×ˢ ({0} : Set ℝ)

/-- The half sheet `e₂` of the transverse cross: the positive part of the axis `x = 0`. -/
def crossRayPosY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1

/-- The half sheet `-e₂` of the transverse cross: the negative part of the axis `x = 0`. -/
def crossRayNegY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 0

/-- Membership in the half sheet `e₁`. -/
theorem mem_crossRayPosX {p : ℝ × ℝ} :
    p ∈ crossRayPosX ↔ (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0 := by
  simp only [crossRayPosX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

/-- Membership in the half sheet `-e₁`. -/
theorem mem_crossRayNegX {p : ℝ × ℝ} :
    p ∈ crossRayNegX ↔ (-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0 := by
  simp only [crossRayNegX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

/-- Membership in the half sheet `e₂`. -/
theorem mem_crossRayPosY {p : ℝ × ℝ} :
    p ∈ crossRayPosY ↔ p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [crossRayPosY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

/-- Membership in the half sheet `-e₂`. -/
theorem mem_crossRayNegY {p : ℝ × ℝ} :
    p ∈ crossRayNegY ↔ p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0) := by
  simp only [crossRayNegY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

/-- The axis `y = 0` is the union of its two half sheets. -/
theorem crossingArcY_eq_union : crossingArcY = crossRayNegX ∪ crossRayPosX := by
  rw [crossingArcY_eq, crossRayNegX, crossRayPosX, ← Set.union_prod,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

/-- The axis `x = 0` is the union of its two half sheets. -/
theorem crossingArcX_eq_union : crossingArcX = crossRayNegY ∪ crossRayPosY := by
  rw [crossingArcX_eq, crossRayNegY, crossRayPosY, ← Set.prod_union,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

/-! ### The bent transverse arcs of the raw cross reglue -/

/-- The first transverse sheet of the raw cross reglue, the bent arc `[e₁, 0] ∪ [0, -e₂]`. -/
def bentArcPos : Set (ℝ × ℝ) := crossRayPosX ∪ crossRayNegY

/-- The second transverse sheet of the raw cross reglue, the bent arc
`[-e₁, 0] ∪ [0, e₂]`. -/
def bentArcNeg : Set (ℝ × ℝ) := crossRayNegX ∪ crossRayPosY

/-- The first bent sheet of the raw cross reglue inside the tube. -/
def bentSheetPos : Set ((ℝ × ℝ) × ℝ) := bentArcPos ×ˢ Icc (0 : ℝ) 1

/-- The second bent sheet of the raw cross reglue inside the tube. -/
def bentSheetNeg : Set ((ℝ × ℝ) × ℝ) := bentArcNeg ×ˢ Icc (0 : ℝ) 1

/-- The configuration of the raw cross reglue inside the tube. -/
def bentFigure : Set ((ℝ × ℝ) × ℝ) := (bentArcPos ∪ bentArcNeg) ×ˢ Icc (0 : ℝ) 1

/-- Membership in the first bent arc. -/
theorem mem_bentArcPos {p : ℝ × ℝ} :
    p ∈ bentArcPos ↔ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0)) := by
  rw [bentArcPos, Set.mem_union, mem_crossRayPosX, mem_crossRayNegY]

/-- Membership in the second bent arc. -/
theorem mem_bentArcNeg {p : ℝ × ℝ} :
    p ∈ bentArcNeg ↔ ((-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)) := by
  rw [bentArcNeg, Set.mem_union, mem_crossRayNegX, mem_crossRayPosY]

/-- The first bent arc lies in the cross section square. -/
theorem bentArcPos_subset_spliceSquare : bentArcPos ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcPos] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨by linarith, h1⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, h0, by linarith⟩

/-- The second bent arc lies in the cross section square. -/
theorem bentArcNeg_subset_spliceSquare : bentArcNeg ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcNeg] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨h0, by linarith⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, by linarith, h2⟩

/-- The two bent arcs of the raw cross reglue cover the old transverse cross: the reglue
changes the pairing of the four half sheets but not the image figure. -/
theorem bentArcPos_union_bentArcNeg :
    bentArcPos ∪ bentArcNeg = crossingArcX ∪ crossingArcY := by
  rw [bentArcPos, bentArcNeg, crossingArcX_eq_union, crossingArcY_eq_union]
  ext p
  simp only [Set.mem_union]
  tauto

/-- The two bent arcs of the raw cross reglue still meet at the centre of the transverse
cross. This is the defect that the resolution below removes. -/
theorem bentArcPos_inter_bentArcNeg : bentArcPos ∩ bentArcNeg = {((0 : ℝ), (0 : ℝ))} := by
  apply Set.Subset.antisymm
  · rintro p ⟨hpos, hneg⟩
    rw [mem_bentArcPos] at hpos
    rw [mem_bentArcNeg] at hneg
    have h1 : p.1 = 0 := by
      rcases hpos with ⟨hp, -⟩ | ⟨hp, -⟩
      · rcases hneg with ⟨hq, -⟩ | ⟨hq, -⟩
        · linarith [hp.1, hq.2]
        · exact hq
      · exact hp
    have h2 : p.2 = 0 := by
      rcases hpos with ⟨-, hp⟩ | ⟨-, hp⟩
      · exact hp
      · rcases hneg with ⟨-, hq⟩ | ⟨-, hq⟩
        · exact hq
        · linarith [hp.2, hq.1]
    exact Prod.ext h1 h2
  · rintro p rfl
    refine ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
      mem_bentArcNeg.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩)⟩

/-- The raw cross reglue has the same image figure inside the tube as the original map. -/
theorem bentFigure_eq_crossingFigure : bentFigure = crossingFigure := by
  rw [bentFigure, crossingFigure, bentArcPos_union_bentArcNeg]

/-- The two bent sheets of the raw cross reglue meet along the whole core curve, so the branch
survives the reglue at every level of the tube. -/
theorem bentSheetPos_inter_bentSheetNeg : bentSheetPos ∩ bentSheetNeg = spliceCore := by
  rw [bentSheetPos, bentSheetNeg, Set.prod_inter_prod, Set.inter_self,
    bentArcPos_inter_bentArcNeg, spliceCore]

/-- The first bent arc meets the lateral boundary of the square in the two points `e₁` and
`-e₂`, the same two points as the chord that replaces it. -/
theorem bentArcPos_inter_spliceSquareBoundary :
    bentArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcPos] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact Or.inr (Prod.ext h1 h)
      · exact absurd h (by intro hx; rw [hx] at h2; linarith)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨mem_bentArcPos.mpr (Or.inr ⟨rfl, le_rfl, by norm_num⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

/-- The second bent arc meets the lateral boundary of the square in the two points `-e₁` and
`e₂`, the same two points as the chord that replaces it. -/
theorem bentArcNeg_inter_spliceSquareBoundary :
    bentArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcNeg] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [hx] at h1; linarith)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inr (Prod.ext h1 h)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcNeg.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨mem_bentArcNeg.mpr (Or.inr ⟨rfl, by norm_num, le_rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

/-- The two bent arcs and the two chords have the same lateral trace, arc by arc. -/
theorem bentArcPos_inter_lateral_eq :
    bentArcPos ∩ spliceSquareBoundary = spliceArcPos ∩ spliceSquareBoundary := by
  rw [bentArcPos_inter_spliceSquareBoundary, spliceArcPos_inter_spliceSquareBoundary]

/-- The two bent arcs and the two chords have the same lateral trace, arc by arc. -/
theorem bentArcNeg_inter_lateral_eq :
    bentArcNeg ∩ spliceSquareBoundary = spliceArcNeg ∩ spliceSquareBoundary := by
  rw [bentArcNeg_inter_spliceSquareBoundary, spliceArcNeg_inter_spliceSquareBoundary]

/-- The raw cross reglue meets the lateral boundary of the tube in `spliceEnds ×ˢ Icc 0 1`,
exactly like the resolution. -/
theorem bentFigure_inter_lateral :
    bentFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [bentFigure_eq_crossingFigure]
  exact crossingFigure_inter_lateral

/-! ### The two bent arcs are polyhedra -/

/-- The first bent arc is a polyhedron. -/
theorem isPolyhedron_bentArcPos : IsPolyhedron bentArcPos :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

/-- The second bent arc is a polyhedron. -/
theorem isPolyhedron_bentArcNeg : IsPolyhedron bentArcNeg :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

/-! ### The chord resolution of the two seams -/

/-- The resolution of the first seam: the affine map of the plane that carries the bent arc
`[e₁, 0] ∪ [0, -e₂]` onto the chord `x - y = 1`, fixing both of its endpoints. -/
noncomputable def crossSeamChordPos (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 + 1) / 2, (p.1 + p.2 - 1) / 2)

/-- The resolution of the second seam: the affine map of the plane that carries the bent arc
`[-e₁, 0] ∪ [0, e₂]` onto the chord `x - y = -1`, fixing both of its endpoints. -/
noncomputable def crossSeamChordNeg (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 - 1) / 2, (p.1 + p.2 + 1) / 2)

/-- The first coordinate of the first chord map. -/
theorem crossSeamChordPos_fst (p : ℝ × ℝ) :
    (crossSeamChordPos p).1 = (p.1 + p.2 + 1) / 2 := rfl

/-- The second coordinate of the first chord map. -/
theorem crossSeamChordPos_snd (p : ℝ × ℝ) :
    (crossSeamChordPos p).2 = (p.1 + p.2 - 1) / 2 := rfl

/-- The first coordinate of the second chord map. -/
theorem crossSeamChordNeg_fst (p : ℝ × ℝ) :
    (crossSeamChordNeg p).1 = (p.1 + p.2 - 1) / 2 := rfl

/-- The second coordinate of the second chord map. -/
theorem crossSeamChordNeg_snd (p : ℝ × ℝ) :
    (crossSeamChordNeg p).2 = (p.1 + p.2 + 1) / 2 := rfl

/-- The first chord map as a bundled affine map of the plane. Its linear part is the rank one
map `v ↦ (v₁ + v₂) • (1 / 2, 1 / 2)`, so the chord map collapses the transverse cross onto the
diagonal direction, which is what straightens the bent arc. -/
noncomputable def crossSeamChordMapPos : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordPos
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordPos] <;> ring

/-- The second chord map as a bundled affine map of the plane. -/
noncomputable def crossSeamChordMapNeg : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordNeg
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordNeg] <;> ring

/-- The first chord map is the restriction of a single affine map of the plane. -/
theorem crossSeamChordMapPos_apply (p : ℝ × ℝ) :
    crossSeamChordMapPos p = crossSeamChordPos p := rfl

/-- The second chord map is the restriction of a single affine map of the plane. -/
theorem crossSeamChordMapNeg_apply (p : ℝ × ℝ) :
    crossSeamChordMapNeg p = crossSeamChordNeg p := rfl

/-- The first resolution fixes the endpoint `e₁` of the bent arc. -/
theorem crossSeamChordPos_apply_posX : crossSeamChordPos ((1 : ℝ), (0 : ℝ)) = (1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

/-- The first resolution fixes the endpoint `-e₂` of the bent arc. -/
theorem crossSeamChordPos_apply_negY : crossSeamChordPos ((0 : ℝ), (-1 : ℝ)) = (0, -1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

/-- The second resolution fixes the endpoint `-e₁` of the bent arc. -/
theorem crossSeamChordNeg_apply_negX : crossSeamChordNeg ((-1 : ℝ), (0 : ℝ)) = (-1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

/-- The second resolution fixes the endpoint `e₂` of the bent arc. -/
theorem crossSeamChordNeg_apply_posY : crossSeamChordNeg ((0 : ℝ), (1 : ℝ)) = (0, 1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

/-- On the first bent arc the linear functional `x + y` takes values in `[-1, 1]`. -/
theorem sum_mem_Icc_of_mem_bentArcPos {p : ℝ × ℝ} (hp : p ∈ bentArcPos) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcPos] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

/-- On the second bent arc the linear functional `x + y` takes values in `[-1, 1]`. -/
theorem sum_mem_Icc_of_mem_bentArcNeg {p : ℝ × ℝ} (hp : p ∈ bentArcNeg) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcNeg] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

/-- The first resolution carries the first bent arc into the chord `x - y = 1`. -/
theorem mapsTo_crossSeamChordPos : MapsTo crossSeamChordPos bentArcPos spliceArcPos := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcPos hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_fst, crossSeamChordPos_snd]; ring

/-- The second resolution carries the second bent arc into the chord `x - y = -1`. -/
theorem mapsTo_crossSeamChordNeg : MapsTo crossSeamChordNeg bentArcNeg spliceArcNeg := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcNeg hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_fst, crossSeamChordNeg_snd]; ring

/-- The first resolution is injective on the first bent arc: on a bent arc the functional
`x + y` separates points. -/
theorem injOn_crossSeamChordPos : InjOn crossSeamChordPos bentArcPos := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordPos_fst, crossSeamChordPos_fst] at h
    linarith
  rw [mem_bentArcPos] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

/-- The second resolution is injective on the second bent arc. -/
theorem injOn_crossSeamChordNeg : InjOn crossSeamChordNeg bentArcNeg := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordNeg_fst, crossSeamChordNeg_fst] at h
    linarith
  rw [mem_bentArcNeg] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

/-- The first resolution covers the whole chord `x - y = 1`. -/
theorem surjOn_crossSeamChordPos : SurjOn crossSeamChordPos bentArcPos spliceArcPos := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(q.1 + q.2, 0), mem_bentArcPos.mpr (Or.inl ⟨⟨hs, ?_⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(0, q.1 + q.2), mem_bentArcPos.mpr (Or.inr ⟨rfl, ?_, le_of_lt hs⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith

/-- The second resolution covers the whole chord `x - y = -1`. -/
theorem surjOn_crossSeamChordNeg : SurjOn crossSeamChordNeg bentArcNeg spliceArcNeg := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(0, q.1 + q.2), mem_bentArcNeg.mpr (Or.inr ⟨rfl, hs, ?_⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(q.1 + q.2, 0), mem_bentArcNeg.mpr (Or.inl ⟨⟨?_, le_of_lt hs⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith

/-- The first resolution is a bijection from the first bent arc onto the chord `x - y = 1`. -/
theorem bijOn_crossSeamChordPos : BijOn crossSeamChordPos bentArcPos spliceArcPos :=
  ⟨mapsTo_crossSeamChordPos, injOn_crossSeamChordPos, surjOn_crossSeamChordPos⟩

/-- The second resolution is a bijection from the second bent arc onto the chord
`x - y = -1`. -/
theorem bijOn_crossSeamChordNeg : BijOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  ⟨mapsTo_crossSeamChordNeg, injOn_crossSeamChordNeg, surjOn_crossSeamChordNeg⟩

/-- The first resolution is piecewise affine on the first bent arc. -/
theorem isPiecewiseAffineOn_crossSeamChordPos :
    IsPiecewiseAffineOn crossSeamChordPos bentArcPos :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapPos
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcPos
      bentArcPos_subset_spliceSquare).congr fun p _ => (crossSeamChordMapPos_apply p).symm

/-- The second resolution is piecewise affine on the second bent arc. -/
theorem isPiecewiseAffineOn_crossSeamChordNeg :
    IsPiecewiseAffineOn crossSeamChordNeg bentArcNeg :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapNeg
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcNeg
      bentArcNeg_subset_spliceSquare).congr fun p _ => (crossSeamChordMapNeg_apply p).symm

/-- **The first seam resolution is a piecewise linear homeomorphism.** It carries the bent arc
`[e₁, 0] ∪ [0, -e₂]` of the raw cross reglue onto the chord `x - y = 1`. -/
theorem isPLHomeomorphOn_crossSeamChordPos :
    IsPLHomeomorphOn crossSeamChordPos bentArcPos spliceArcPos :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcPos
    isPiecewiseAffineOn_crossSeamChordPos bijOn_crossSeamChordPos

/-- **The second seam resolution is a piecewise linear homeomorphism.** It carries the bent
arc `[-e₁, 0] ∪ [0, e₂]` of the raw cross reglue onto the chord `x - y = -1`. -/
theorem isPLHomeomorphOn_crossSeamChordNeg :
    IsPLHomeomorphOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcNeg
    isPiecewiseAffineOn_crossSeamChordNeg bijOn_crossSeamChordNeg

/-! ### Both the bent arcs and the chords are piecewise linear arcs -/

/-- The chord `x - y = 1` is the straight segment from `-e₂` to `e₁`. -/
theorem spliceArcPos_eq_segment :
    spliceArcPos = segment ℝ ((0 : ℝ), (-1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
  rw [spliceArcPos_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((0 : ℝ), (-1 : ℝ)) + t • ((1 : ℝ), (0 : ℝ))
      = ((1 - t) * 0 + t * 1, (1 - t) * (-1) + t * 0) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

/-- The chord `x - y = -1` is the straight segment from `-e₁` to `e₂`. -/
theorem spliceArcNeg_eq_segment :
    spliceArcNeg = segment ℝ ((-1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
  rw [spliceArcNeg_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((-1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ))
      = ((1 - t) * (-1) + t * 0, (1 - t) * 0 + t * 1) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

/-- The first chord is a piecewise linear arc. -/
theorem isPLBall_spliceArcPos : IsPLBall 1 spliceArcPos := by
  rw [spliceArcPos_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

/-- The second chord is a piecewise linear arc. -/
theorem isPLBall_spliceArcNeg : IsPLBall 1 spliceArcNeg := by
  rw [spliceArcNeg_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

/-- The first bent arc of the raw cross reglue is a piecewise linear arc, carried onto the
first chord by the resolution. -/
theorem isPLBall_bentArcPos : IsPLBall 1 bentArcPos :=
  isPLBall_spliceArcPos.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordPos.symm

/-- The second bent arc of the raw cross reglue is a piecewise linear arc. -/
theorem isPLBall_bentArcNeg : IsPLBall 1 bentArcNeg :=
  isPLBall_spliceArcNeg.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordNeg.symm

/-- The first bent sheet of the raw cross reglue is a piecewise linear disk. -/
theorem isPLBall_bentSheetPos : IsPLBall 2 bentSheetPos :=
  isPLBall_two_prod isPLBall_bentArcPos (isPLBall_Icc zero_lt_one)

/-- The second bent sheet of the raw cross reglue is a piecewise linear disk. -/
theorem isPLBall_bentSheetNeg : IsPLBall 2 bentSheetNeg :=
  isPLBall_two_prod isPLBall_bentArcNeg (isPLBall_Icc zero_lt_one)

/-- The first replacement sheet is a piecewise linear disk. -/
theorem isPLBall_spliceSheetPos : IsPLBall 2 spliceSheetPos :=
  isPLBall_two_prod isPLBall_spliceArcPos (isPLBall_Icc zero_lt_one)

/-- The second replacement sheet is a piecewise linear disk. -/
theorem isPLBall_spliceSheetNeg : IsPLBall 2 spliceSheetNeg :=
  isPLBall_two_prod isPLBall_spliceArcNeg (isPLBall_Icc zero_lt_one)

/-! ### The fiberwise resolution along the base interval -/

/-- The fiberwise resolution of the first seam along the base interval of the tube. -/
noncomputable def crossSeamResolvePos : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordPos id

/-- The fiberwise resolution of the second seam along the base interval of the tube. -/
noncomputable def crossSeamResolveNeg : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordNeg id

/-- The fiberwise resolution acts on the cross section only. -/
theorem crossSeamResolvePos_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolvePos p).1 = crossSeamChordPos p.1 := rfl

/-- The fiberwise resolution does not move the base coordinate. This is the formal statement
that the replacement is a product along the base interval, so that, the base being an interval
and not a circle, no period identification and no sheet exchange can intervene. -/
theorem crossSeamResolvePos_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolvePos p).2 = p.2 := rfl

/-- The fiberwise resolution acts on the cross section only. -/
theorem crossSeamResolveNeg_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolveNeg p).1 = crossSeamChordNeg p.1 := rfl

/-- The fiberwise resolution does not move the base coordinate. -/
theorem crossSeamResolveNeg_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolveNeg p).2 = p.2 := rfl

/-- **The fiberwise resolution of the first seam is a piecewise linear homeomorphism** from
the first bent sheet of the raw cross reglue onto the first replacement sheet. -/
theorem isPLHomeomorphOn_crossSeamResolvePos :
    IsPLHomeomorphOn crossSeamResolvePos bentSheetPos spliceSheetPos :=
  isPLHomeomorphOn_crossSeamChordPos.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

/-- **The fiberwise resolution of the second seam is a piecewise linear homeomorphism** from
the second bent sheet of the raw cross reglue onto the second replacement sheet. -/
theorem isPLHomeomorphOn_crossSeamResolveNeg :
    IsPLHomeomorphOn crossSeamResolveNeg bentSheetNeg spliceSheetNeg :=
  isPLHomeomorphOn_crossSeamChordNeg.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

/-- **The resolution removes the branch.** The two bent sheets of the raw cross reglue meet
along the whole core curve, while their images under the fiberwise resolution are disjoint. -/
theorem disjoint_image_crossSeamResolve :
    Disjoint (crossSeamResolvePos '' bentSheetPos) (crossSeamResolveNeg '' bentSheetNeg) := by
  rw [isPLHomeomorphOn_crossSeamResolvePos.bijOn.image_eq,
    isPLHomeomorphOn_crossSeamResolveNeg.bijOn.image_eq]
  exact disjoint_spliceSheetPos_spliceSheetNeg

/-- **The four lateral attaching intervals are unchanged.** On the part of the first bent
sheet lying over the lateral boundary of the square the resolution is the identity. -/
theorem crossSeamResolvePos_eqOn_lateral :
    EqOn crossSeamResolvePos id (bentSheetPos ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcPos ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcPos_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolvePos_snd p)
  rw [crossSeamResolvePos_fst]
  change crossSeamChordPos p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordPos_apply_posX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordPos_apply_negY

/-- **The four lateral attaching intervals are unchanged.** On the part of the second bent
sheet lying over the lateral boundary of the square the resolution is the identity. -/
theorem crossSeamResolveNeg_eqOn_lateral :
    EqOn crossSeamResolveNeg id (bentSheetNeg ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcNeg ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcNeg_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolveNeg_snd p)
  rw [crossSeamResolveNeg_fst]
  change crossSeamChordNeg p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordNeg_apply_negX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordNeg_apply_posY

/-- The cross section square is convex. -/
theorem convex_spliceSquare : Convex ℝ spliceSquare :=
  (convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)

/-- **The resolution is supported in the cross section disks.** Every point of the first bent
sheet is moved to its image along a segment contained in the cross section disk through it,
so in particular at the two ends of the tube the boundary curves move inside the end disks
only. -/
theorem segment_crossSeamResolvePos_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetPos) :
    segment ℝ p (crossSeamResolvePos p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcPos_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolvePos_snd p⟩
    rw [crossSeamResolvePos_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordPos hp.1)

/-- **The resolution is supported in the cross section disks.** Every point of the second bent
sheet is moved to its image along a segment contained in the cross section disk through it. -/
theorem segment_crossSeamResolveNeg_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetNeg) :
    segment ℝ p (crossSeamResolveNeg p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcNeg_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolveNeg_snd p⟩
    rw [crossSeamResolveNeg_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordNeg hp.1)

/-! ### The resolution deletes exactly the branch -/

/-- The old figure inside the tube is the union of the two bent sheets. -/
theorem bentFigure_eq_union : bentFigure = bentSheetPos ∪ bentSheetNeg := by
  rw [bentFigure, bentSheetPos, bentSheetNeg, Set.union_prod]

/-- The replacement figure inside the tube is the union of the two chord sheets. -/
theorem spliceFigure_eq_union : spliceFigure = spliceSheetPos ∪ spliceSheetNeg := by
  rw [spliceFigure, spliceSheetPos, spliceSheetNeg, Set.union_prod]

/-- The source of the model: two disjoint strips, one for each of the two source strips of the
raw cross reglue that meet the tube. -/
def bentSource : Set (Bool × ((ℝ × ℝ) × ℝ)) :=
  {true} ×ˢ bentSheetPos ∪ {false} ×ˢ bentSheetNeg

/-- Membership in the source of the model. -/
theorem mem_bentSource {q : Bool × ((ℝ × ℝ) × ℝ)} :
    q ∈ bentSource ↔
      (q.1 = true ∧ q.2 ∈ bentSheetPos) ∨ (q.1 = false ∧ q.2 ∈ bentSheetNeg) := by
  simp only [bentSource, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff]

/-- The raw cross reglued map of the model: each of the two source strips is sent to its bent
sheet inside the tube. -/
def crossSeamInclude (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ := q.2

/-- The resolved map of the model: each of the two source strips is sent to its chord sheet
inside the tube. Note that this changes the map on the two source strips; it is not an ambient
postcomposition, which could never delete a branch. -/
noncomputable def crossSeamResolve (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ :=
  if q.1 then crossSeamResolvePos q.2 else crossSeamResolveNeg q.2

/-- The resolved map on the first source strip. -/
theorem crossSeamResolve_true (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (true, x) = crossSeamResolvePos x := rfl

/-- The resolved map on the second source strip. -/
theorem crossSeamResolve_false (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (false, x) = crossSeamResolveNeg x := rfl

/-- **The resolved map is injective.** On each source strip the resolution is a piecewise
linear homeomorphism, and the two chord sheets are disjoint. -/
theorem injOn_crossSeamResolve : InjOn crossSeamResolve bentSource := by
  rintro ⟨b, x⟩ hq ⟨b', x'⟩ hr hqr
  rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;>
    rcases mem_bentSource.mp hr with ⟨hb', hx'⟩ | ⟨hb', hx'⟩ <;>
      subst hb <;> subst hb'
  · rw [crossSeamResolve_true, crossSeamResolve_true] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.injOn hx hx' hqr)
  · exfalso
    rw [crossSeamResolve_true, crossSeamResolve_false] at hqr
    have h1 : crossSeamResolvePos x ∈ spliceSheetPos :=
      isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg h1
      (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx')
  · exfalso
    rw [crossSeamResolve_false, crossSeamResolve_true] at hqr
    have h1 : crossSeamResolveNeg x ∈ spliceSheetNeg :=
      isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg
      (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx') h1
  · rw [crossSeamResolve_false, crossSeamResolve_false] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.injOn hx hx' hqr)

/-- **The raw cross reglue keeps the branch.** Its double point set inside the tube is the
whole core curve, at every level of the tube. -/
theorem doublePointSet_crossSeamInclude :
    doublePointSet crossSeamInclude bentSource = spliceCore := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨b, x⟩, hq, ⟨b', x'⟩, hr, hne, hy1, hy2⟩
    have hx : x = y := hy1
    have hx' : x' = y := hy2
    have hbb : b ≠ b' := fun h => hne (Prod.ext h (hx.trans hx'.symm))
    rw [← bentSheetPos_inter_bentSheetNeg]
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩ <;>
      rcases mem_bentSource.mp hr with ⟨hb', hs'⟩ | ⟨hb', hs'⟩
    · exact absurd (hb.trans hb'.symm) hbb
    · exact ⟨hx ▸ hs, hx' ▸ hs'⟩
    · exact ⟨hx' ▸ hs', hx ▸ hs⟩
    · exact absurd (hb.trans hb'.symm) hbb
  · intro y hy
    rw [← bentSheetPos_inter_bentSheetNeg] at hy
    exact ⟨(true, y), mem_bentSource.mpr (Or.inl ⟨rfl, hy.1⟩), (false, y),
      mem_bentSource.mpr (Or.inr ⟨rfl, hy.2⟩),
      fun h => Bool.noConfusion (congrArg Prod.fst h), rfl, rfl⟩

/-- **The resolution deletes the branch and creates no other double point.** Inside the tube
the resolved map has no double point at all, whereas the raw cross reglue had the whole core
curve. Together with the fact that the resolution is the identity on the lateral boundary,
this is the exact model form of the equality of singular sets. -/
theorem doublePointSet_crossSeamResolve :
    doublePointSet crossSeamResolve bentSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn crossSeamResolve bentSource).mpr injOn_crossSeamResolve

/-- The raw cross reglue covers the old figure inside the tube. -/
theorem image_crossSeamInclude : crossSeamInclude '' bentSource = bentFigure := by
  rw [bentFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro x (hx | hx)
    · exact ⟨(true, x), mem_bentSource.mpr (Or.inl ⟨rfl, hx⟩), rfl⟩
    · exact ⟨(false, x), mem_bentSource.mpr (Or.inr ⟨rfl, hx⟩), rfl⟩

/-- The resolved map covers the replacement figure inside the tube. -/
theorem image_crossSeamResolve : crossSeamResolve '' bentSource = spliceFigure := by
  rw [spliceFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨⟨b, z⟩, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨hb, h⟩ | ⟨hb, h⟩ <;> subst hb
    · exact Or.inl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo h)
    · exact Or.inr (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo h)
  · rintro x (hx | hx)
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolvePos.bijOn.surjOn hx
      exact ⟨(true, z), mem_bentSource.mpr (Or.inl ⟨rfl, hz⟩), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolveNeg.bijOn.surjOn hx
      exact ⟨(false, z), mem_bentSource.mpr (Or.inr ⟨rfl, hz⟩), rfl⟩

/-! ### Branch descent from a branch correspondence -/

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

/-- **Descent from an exact branch correspondence.** If the branches of `T'` correspond
bijectively to the branches of `T` other than `c`, then the complexity drops strictly. This is
the form in which a surgery that deletes exactly one branch, such as the cross seam
resolution, feeds `complexity_lt_of_injective_origin`. -/
theorem complexity_lt_of_branchEquiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') {c : T.Branch}
    (e : T'.Branch ≃ {b : T.Branch // b ≠ c}) :
    T'.complexity < T.complexity :=
  T.complexity_lt_of_injective_origin T' c (fun b => (e b).1)
    (fun _ _ h => e.injective (Subtype.ext h)) fun b => (e b).2

end NormalSingularSetTriangulation

/-! ### The contract of a geometric cross seam resolution -/

/-- The data that a geometric resolution of the two new seams of the boundary cross reglue has
to supply: a normal singular two cell whose double point set is exactly the old one with the
carrier of the branch `c` removed, a bijection between its branches and the old branches other
than `c` that preserves branch carriers, and the control that the new image stays inside the
old image together with the resolving tube `U`.

The image control is stated with `U` because the resolved map is *not* a reparametrisation of
the reglued map: it changes the map on two source strips, and an ambient postcomposition could
never delete a branch, since an ambient homeomorphism preserves every coincidence of values.
Correspondingly the resolved image is in general not contained in the old image. -/
structure CrossSeamResolutionData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  /-- The resolved singular two cell. -/
  cell : SingularTwoCell M
  /-- The resolved cell is again normal over the same boundary data. -/
  normal : NormalSingularCellData cell BdM B
  /-- The resolution deletes exactly the carrier of the branch `c` from the double point
  set. -/
  doublePointSet_eq : doublePointSet cell cell.domain =
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c
  /-- The branches of the resolved cell correspond to the old branches other than `c`. -/
  branchEquiv : normal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}
  /-- The correspondence preserves branch carriers. -/
  branchCarrier_eq : ∀ b, normal.singularSet.branchCarrier b =
    hD.singularSet.branchCarrier (branchEquiv b).1
  /-- The resolved image stays inside the old image together with the resolving tube. -/
  image_subset : cell '' cell.domain ⊆ D '' D.domain ∪ U

namespace CrossSeamResolutionData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

/-- **The complexity drops strictly.** This is the descent that Moise's induction consumes;
it uses the branch correspondence, not merely the inclusion of double point sets, because a
subset of an arc can split into two arcs and so raise the branch count. -/
theorem complexity_lt (R : CrossSeamResolutionData hD c U) :
    R.normal.singularSet.complexity < hD.singularSet.complexity :=
  hD.singularSet.complexity_lt_of_branchEquiv_compl R.normal.singularSet R.branchEquiv

/-- The resolved cell has no new double points. -/
theorem doublePointSet_subset (R : CrossSeamResolutionData hD c U) :
    doublePointSet R.cell R.cell.domain ⊆ doublePointSet D D.domain := by
  rw [R.doublePointSet_eq]
  exact Set.sdiff_subset

/-- The resolved cell has no double point on the carrier of the resolved branch: the branch
really is gone, in contrast with the conclusion of the raw cross reglue. -/
theorem disjoint_branchCarrier (R : CrossSeamResolutionData hD c U) :
    Disjoint (doublePointSet R.cell R.cell.domain) (hD.singularSet.branchCarrier c) := by
  rw [R.doublePointSet_eq]
  exact Set.disjoint_sdiff_left

/-- Every branch carrier of the resolved cell is a branch carrier of the old one. -/
theorem branchCarrier_mem_range (R : CrossSeamResolutionData hD c U)
    (b : R.normal.singularSet.Branch) :
    R.normal.singularSet.branchCarrier b ∈
      Set.range (hD.singularSet.branchCarrier ∘ fun b' : {b' // b' ≠ c} => b'.1) :=
  ⟨R.branchEquiv b, (R.branchCarrier_eq b).symm⟩

end CrossSeamResolutionData

end DifferentialGeometry.Topology.PiecewiseLinear
