/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Product

/-!
# The cylinder splice of the first closed branch case

Moise's Lemma 2 treats a closed branch whose preimage is a single circle doubly covering the
image circle by replacing the source annulus along a cylinder splice. This file builds the
model of that splice and proves the properties that make the replacement legitimate.

The model is the square cylinder `spliceCylinder = spliceSquare ×ˢ Icc 0 1` together with the
period identification `SpliceRel`, which glues `(x, y, 0)` to `(y, x, 1)`. The end map is
`Prod.swap`, so this is a mapping torus with sheet exchange and not a product. There is no
injective chart of a whole closed branch onto a straight axis, and none is used here.

* `crossingArcX`, `crossingArcY`, `crossingSheetX`, `crossingSheetY` and `crossingFigure` are
  the old configuration: the two crossing rectangles coming from the source annulus.
* `spliceArcPos`, `spliceArcNeg`, `spliceSheetPos`, `spliceSheetNeg` and `spliceFigure` are
  Moise's replacement: the traces of the planes `x - y = 1` and `x - y = -1`.

The main results are the following.

* `crossingSheetX_inter_crossingSheetY` : the old configuration meets itself along the whole
  core curve `spliceCore`, hence at every level of the cylinder.
* `disjoint_spliceSheetPos_spliceSheetNeg` and
  `image_spliceSheetPos_inter_image_spliceSheetNeg` : the replacement is disjoint from itself
  before splicing, and after splicing its two sheets meet exactly in the images of the two
  glued end arcs.
* `crossingFigure_inter_lateral` and `spliceFigure_inter_lateral` : both configurations meet
  the lateral boundary of the cylinder in the same set `spliceEnds ×ˢ Icc 0 1`, which is what
  lets the replacement be glued in.
* `swap_mem_crossingArcY_of_mem_crossingArcX`, `swap_mem_spliceArcNeg_of_mem_spliceArcPos`,
  `swap_ne_self_of_mem_spliceEnds` and `spliceMk_core_zero_eq_one` : the period map fixes the
  core but moves every lateral boundary point, which is the formal content of a single
  preimage circle double covering the branch circle.

The spliced cylinder itself is the quotient `Quotient spliceSetoid`, with quotient map
`spliceMk`; `spliceMk_eq_iff` identifies the fibres with `SpliceRel`. The identification is
not an ad hoc choice: `spliceRel_iff_of_isCylindricalDiagram` shows that a cylindrical diagram
over the square whose end map is the coordinate swap identifies exactly the `SpliceRel` pairs.
That last statement is conditional, since no such diagram is constructed here.

Not proved here: that `spliceFigure` becomes an annulus in the spliced cylinder. That needs a
piecewise linear homeomorphism from a standard annulus onto the image of `spliceFigure`, which
this file does not construct; the results below give the embeddedness, the boundary matching
and the double cover that such a construction would consume.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-! ### The square cylinder -/

/-- The square `[-1, 1] × [-1, 1]`, the piecewise linear model of the disk cross-section of
the cylinder that is spliced. -/
def spliceSquare : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

/-- Membership in the square model of the disk. -/
theorem mem_spliceSquare {p : ℝ × ℝ} :
    p ∈ spliceSquare ↔ (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [spliceSquare, Set.mem_prod, Set.mem_Icc]

/-- The unglued cylinder `D² × [0, 1]` whose ends the splice identifies. -/
def spliceCylinder : Set ((ℝ × ℝ) × ℝ) := spliceSquare ×ˢ Icc (0 : ℝ) 1

/-- Membership in the unglued cylinder. -/
theorem mem_spliceCylinder {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceCylinder ↔ p.1 ∈ spliceSquare ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

/-- The square model of the disk is a bounded intersection of half-spaces. -/
theorem isHPolytope_spliceSquare : IsHPolytope spliceSquare :=
  isHPolytope_Icc.prod isHPolytope_Icc

/-- The unglued cylinder is a bounded intersection of half-spaces. -/
theorem isHPolytope_spliceCylinder : IsHPolytope spliceCylinder :=
  isHPolytope_spliceSquare.prod isHPolytope_Icc

/-- The square model of the disk has nonempty interior. -/
theorem interior_spliceSquare_nonempty : (interior spliceSquare).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  rw [spliceSquare]
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

/-- The unglued cylinder has nonempty interior. -/
theorem interior_spliceCylinder_nonempty : (interior spliceCylinder).Nonempty := by
  refine ⟨((0, 0), 1 / 2), ?_⟩
  rw [spliceCylinder, spliceSquare]
  simp only [interior_prod_eq, interior_Icc, Set.mem_prod, Set.mem_Ioo]
  norm_num

/-- The square model of the disk is a piecewise linear two-dimensional ball. -/
theorem isPLBall_spliceSquare : IsPLBall 2 spliceSquare := by
  have h := isHPolytope_spliceSquare.isPLBall interior_spliceSquare_nonempty
  rwa [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp] at h

/-- The unglued cylinder is a piecewise linear three-dimensional ball. -/
theorem isPLBall_spliceCylinder : IsPLBall 3 spliceCylinder := by
  have h := isHPolytope_spliceCylinder.isPLBall interior_spliceCylinder_nonempty
  rwa [show Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 by simp] at h

/-- The lateral boundary of the square model of the disk. -/
def spliceSquareBoundary : Set (ℝ × ℝ) :=
  {p ∈ spliceSquare | p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1}

/-- Membership in the lateral boundary of the square. -/
theorem mem_spliceSquareBoundary {p : ℝ × ℝ} :
    p ∈ spliceSquareBoundary ↔
      p ∈ spliceSquare ∧ (p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1) := Iff.rfl

/-- The lateral boundary of the square is exactly its topological frontier, so the name is
the geometric one. -/
theorem spliceSquareBoundary_eq_frontier : spliceSquareBoundary = frontier spliceSquare := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  rw [spliceSquare, frontier_prod_eq, closure_Icc, frontier_Icc hle]
  ext p
  simp only [spliceSquareBoundary, spliceSquare, Set.mem_prod, Set.mem_Icc,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    rcases h with h | h | h | h
    · exact Or.inr ⟨Or.inl h, h3, h4⟩
    · exact Or.inr ⟨Or.inr h, h3, h4⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inl h⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inr h⟩
  · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨h, h3, h4⟩)
    · rcases h with h | h
      · exact ⟨⟨⟨h1, h2⟩, by norm_num [h], by norm_num [h]⟩, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨⟨⟨h1, h2⟩, by norm_num [h], by norm_num [h]⟩, Or.inr (Or.inr (Or.inr h))⟩
    · rcases h with h | h
      · exact ⟨⟨⟨by norm_num [h], by norm_num [h]⟩, h3, h4⟩, Or.inl h⟩
      · exact ⟨⟨⟨by norm_num [h], by norm_num [h]⟩, h3, h4⟩, Or.inr (Or.inl h)⟩

/-! ### The period identification -/

/-- The period identification of the cylinder splice: the bottom point `(x, y, 0)` is glued
to the top point `(y, x, 1)`. The two coordinates of the cross-section are exchanged, so the
end map is `Prod.swap`. -/
def SpliceRel (p q : (ℝ × ℝ) × ℝ) : Prop :=
  p = q ∨ (p.2 = 0 ∧ q.2 = 1 ∧ q.1 = p.1.swap) ∨ (p.2 = 1 ∧ q.2 = 0 ∧ p.1 = q.1.swap)

/-- The period identification is an equivalence relation. -/
theorem spliceRel_equivalence : Equivalence SpliceRel := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
  · rintro p q (rfl | ⟨h0, h1, hq⟩ | ⟨h1, h0, hp⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨h1, h0, hq⟩)
    · exact Or.inr (Or.inl ⟨h0, h1, hp⟩)
  · rintro p q r (rfl | ⟨hp0, hq1, hq⟩ | ⟨hp1, hq0, hp⟩) hqr
    · exact hqr
    · rcases hqr with rfl | ⟨hq0, -, -⟩ | ⟨-, hr0, hq'⟩
      · exact Or.inr (Or.inl ⟨hp0, hq1, hq⟩)
      · exact absurd (hq0.symm.trans hq1) (by norm_num)
      · refine Or.inl (Prod.ext ?_ (hp0.trans hr0.symm))
        have hswap : p.1.swap = r.1.swap := hq.symm.trans hq'
        have := congrArg Prod.swap hswap
        simpa using this
    · rcases hqr with rfl | ⟨-, hr1, hr⟩ | ⟨hq1, -, -⟩
      · exact Or.inr (Or.inr ⟨hp1, hq0, hp⟩)
      · refine Or.inl (Prod.ext ?_ (hp1.trans hr1.symm))
        have hswap : p.1 = r.1 := hp.trans hr.symm
        exact hswap
      · exact absurd (hq0.symm.trans hq1) (by norm_num)

/-- The period identification as a setoid on the ambient space of the cylinder. -/
def spliceSetoid : Setoid ((ℝ × ℝ) × ℝ) := ⟨SpliceRel, spliceRel_equivalence⟩

/-- The spliced cylinder is the quotient of the ambient space by the period identification;
this is its quotient map. -/
def spliceMk (p : (ℝ × ℝ) × ℝ) : Quotient spliceSetoid := Quotient.mk spliceSetoid p

/-- Two points have the same image in the spliced cylinder exactly when they are related by
the period identification. -/
theorem spliceMk_eq_iff {p q : (ℝ × ℝ) × ℝ} : spliceMk p = spliceMk q ↔ SpliceRel p q := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Away from the two ends the period identification is trivial, so the splice creates no
identification at an interior level of the cylinder. -/
theorem eq_of_spliceRel_of_snd_ne {p q : (ℝ × ℝ) × ℝ} (h0 : p.2 ≠ 0) (h1 : p.2 ≠ 1)
    (h : SpliceRel p q) : p = q := by
  rcases h with h | ⟨hp0, -, -⟩ | ⟨hp1, -, -⟩
  · exact h
  · exact absurd hp0 h0
  · exact absurd hp1 h1

/-! ### The old crossing configuration and its replacement -/

/-- The cross-section `x = 0` of the first of the two crossing rectangles. -/
def crossingArcX : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 = 0}

/-- The cross-section `y = 0` of the second of the two crossing rectangles. -/
def crossingArcY : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.2 = 0}

/-- The cross-section `x - y = 1` of the first replacement sheet. -/
def spliceArcPos : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 - p.2 = 1}

/-- The cross-section `x - y = -1` of the second replacement sheet. -/
def spliceArcNeg : Set (ℝ × ℝ) := {p ∈ spliceSquare | p.1 - p.2 = -1}

/-- The rectangle `x = 0` of the old configuration. -/
def crossingSheetX : Set ((ℝ × ℝ) × ℝ) := crossingArcX ×ˢ Icc (0 : ℝ) 1

/-- The rectangle `y = 0` of the old configuration. -/
def crossingSheetY : Set ((ℝ × ℝ) × ℝ) := crossingArcY ×ˢ Icc (0 : ℝ) 1

/-- The old configuration: the two crossing rectangles coming from the source annulus. -/
def crossingFigure : Set ((ℝ × ℝ) × ℝ) := (crossingArcX ∪ crossingArcY) ×ˢ Icc (0 : ℝ) 1

/-- The trace of the plane `x - y = 1` on the cylinder. -/
def spliceSheetPos : Set ((ℝ × ℝ) × ℝ) := spliceArcPos ×ˢ Icc (0 : ℝ) 1

/-- The trace of the plane `x - y = -1` on the cylinder. -/
def spliceSheetNeg : Set ((ℝ × ℝ) × ℝ) := spliceArcNeg ×ˢ Icc (0 : ℝ) 1

/-- Moise's replacement figure: the traces of the two planes `x - y = 1` and `x - y = -1`. -/
def spliceFigure : Set ((ℝ × ℝ) × ℝ) := (spliceArcPos ∪ spliceArcNeg) ×ˢ Icc (0 : ℝ) 1

/-- The core curve of the cylinder, the axis along which the old configuration crosses
itself. -/
def spliceCore : Set ((ℝ × ℝ) × ℝ) := ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1

/-- The four points of the square at which either configuration meets the lateral boundary of
the cylinder. -/
def spliceEnds : Set (ℝ × ℝ) := {(0, 1), (0, -1), (1, 0), (-1, 0)}

/-- Membership in the rectangle `x = 0`. -/
theorem mem_crossingSheetX {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingSheetX ↔ p.1 ∈ crossingArcX ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

/-- Membership in the rectangle `y = 0`. -/
theorem mem_crossingSheetY {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingSheetY ↔ p.1 ∈ crossingArcY ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

/-- Membership in the first replacement sheet. -/
theorem mem_spliceSheetPos {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceSheetPos ↔ p.1 ∈ spliceArcPos ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

/-- Membership in the second replacement sheet. -/
theorem mem_spliceSheetNeg {p : (ℝ × ℝ) × ℝ} :
    p ∈ spliceSheetNeg ↔ p.1 ∈ spliceArcNeg ∧ p.2 ∈ Icc (0 : ℝ) 1 := Set.mem_prod

/-! ### The cross-sections are arcs -/

/-- The cross-section `x = 0` is the vertical arc of the square. -/
theorem crossingArcX_eq : crossingArcX = ({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1 := by
  ext p
  simp only [crossingArcX, mem_spliceSquare, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h⟩
    exact ⟨h, h2⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨by norm_num [h], h2⟩, h⟩

/-- The cross-section `y = 0` is the horizontal arc of the square. -/
theorem crossingArcY_eq : crossingArcY = Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ) := by
  ext p
  simp only [crossingArcY, mem_spliceSquare, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h⟩
    exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩
    exact ⟨⟨h1, by norm_num [h], by norm_num [h]⟩, h⟩

/-- The cross-section `x - y = 1` is the arc from `(0, -1)` to `(1, 0)`. -/
theorem spliceArcPos_eq : spliceArcPos = (fun t : ℝ => (t, t - 1)) '' Icc (0 : ℝ) 1 := by
  ext p
  simp only [spliceArcPos, mem_spliceSquare, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    exact ⟨p.1, ⟨by linarith, h2⟩, Prod.ext rfl (by simp; linarith)⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨⟨⟨by linarith, ht1⟩, by simp; linarith, by simp; linarith⟩, by simp⟩

/-- The cross-section `x - y = -1` is the arc from `(-1, 0)` to `(0, 1)`. -/
theorem spliceArcNeg_eq : spliceArcNeg = (fun t : ℝ => (t - 1, t)) '' Icc (0 : ℝ) 1 := by
  ext p
  simp only [spliceArcNeg, mem_spliceSquare, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h⟩
    exact ⟨p.2, ⟨by linarith, h4⟩, Prod.ext (by simp; linarith) rfl⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨⟨⟨by simp; linarith, by simp; linarith⟩, by linarith, ht1⟩, by simp⟩

/-! ### The old configuration crosses itself, the replacement does not -/

/-- The two crossing arcs meet in the origin of the square. -/
theorem crossingArcX_inter_crossingArcY :
    crossingArcX ∩ crossingArcY = {((0 : ℝ), (0 : ℝ))} := by
  ext p
  simp only [crossingArcX, crossingArcY, Set.mem_inter_iff, Set.mem_sep_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨-, h1⟩, -, h2⟩
    exact Prod.ext h1 h2
  · rintro rfl
    refine ⟨⟨?_, rfl⟩, ⟨?_, rfl⟩⟩ <;> simp only [mem_spliceSquare] <;> norm_num

/-- The two rectangles of the old configuration meet along the whole core curve, hence at
every level of the cylinder. This is the double curve that the splice must remove. -/
theorem crossingSheetX_inter_crossingSheetY :
    crossingSheetX ∩ crossingSheetY = spliceCore := by
  rw [crossingSheetX, crossingSheetY, Set.prod_inter_prod, Set.inter_self,
    crossingArcX_inter_crossingArcY, spliceCore]

/-- Every level of the cylinder carries a double point of the old configuration. -/
theorem mem_crossingSheet_inter {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((0 : ℝ), (0 : ℝ)), t) ∈ crossingSheetX ∩ crossingSheetY := by
  rw [crossingSheetX_inter_crossingSheetY]
  exact ⟨rfl, ht⟩

/-- The core curve is nonempty. -/
theorem spliceCore_nonempty : spliceCore.Nonempty :=
  ⟨(((0 : ℝ), (0 : ℝ)), 0), rfl, by norm_num⟩

/-- The two replacement arcs are disjoint: the planes `x - y = 1` and `x - y = -1` never
meet. -/
theorem disjoint_spliceArcPos_spliceArcNeg : Disjoint spliceArcPos spliceArcNeg := by
  rw [Set.disjoint_left]
  rintro p ⟨-, hp⟩ ⟨-, hq⟩
  rw [hp] at hq
  norm_num at hq

/-- The two replacement sheets are disjoint, so Moise's figure has no double point inside the
unglued cylinder. -/
theorem disjoint_spliceSheetPos_spliceSheetNeg : Disjoint spliceSheetPos spliceSheetNeg := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact Set.disjoint_left.mp disjoint_spliceArcPos_spliceArcNeg
    (mem_spliceSheetPos.mp hp).1 (mem_spliceSheetNeg.mp hq).1

/-! ### The sheet exchange across the period -/

/-- The swap carries the square to itself. -/
theorem swap_mem_spliceSquare {p : ℝ × ℝ} (hp : p ∈ spliceSquare) : p.swap ∈ spliceSquare := by
  rw [mem_spliceSquare] at hp ⊢
  exact ⟨hp.2, hp.1⟩

/-- Running once around the period carries the sheet `x = 0` to the sheet `y = 0`. -/
theorem swap_mem_crossingArcY_of_mem_crossingArcX {p : ℝ × ℝ} (hp : p ∈ crossingArcX) :
    p.swap ∈ crossingArcY :=
  ⟨swap_mem_spliceSquare hp.1, hp.2⟩

/-- Running once around the period carries the sheet `y = 0` back to the sheet `x = 0`. -/
theorem swap_mem_crossingArcX_of_mem_crossingArcY {p : ℝ × ℝ} (hp : p ∈ crossingArcY) :
    p.swap ∈ crossingArcX :=
  ⟨swap_mem_spliceSquare hp.1, hp.2⟩

/-- Running once around the period carries the plane `x - y = 1` to the plane
`x - y = -1`. -/
theorem swap_mem_spliceArcNeg_of_mem_spliceArcPos {p : ℝ × ℝ} (hp : p ∈ spliceArcPos) :
    p.swap ∈ spliceArcNeg :=
  ⟨swap_mem_spliceSquare hp.1, by
    have h := hp.2
    change p.2 - p.1 = -1
    linarith⟩

/-- Running once around the period carries the plane `x - y = -1` back to the plane
`x - y = 1`. -/
theorem swap_mem_spliceArcPos_of_mem_spliceArcNeg {p : ℝ × ℝ} (hp : p ∈ spliceArcNeg) :
    p.swap ∈ spliceArcPos :=
  ⟨swap_mem_spliceSquare hp.1, by
    have h := hp.2
    change p.2 - p.1 = 1
    linarith⟩

/-- The period map exchanges the two sheets of the old configuration. -/
theorem swap_image_crossingArcX : Prod.swap '' crossingArcX = crossingArcY := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_crossingArcY_of_mem_crossingArcX hq
  · intro p hp
    exact ⟨p.swap, swap_mem_crossingArcX_of_mem_crossingArcY hp, Prod.swap_swap p⟩

/-- The period map exchanges the two replacement sheets. -/
theorem swap_image_spliceArcPos : Prod.swap '' spliceArcPos = spliceArcNeg := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact swap_mem_spliceArcNeg_of_mem_spliceArcPos hq
  · intro p hp
    exact ⟨p.swap, swap_mem_spliceArcPos_of_mem_spliceArcNeg hp, Prod.swap_swap p⟩

/-- The exchange is not trivial: the two sheets of the old configuration are distinct. -/
theorem crossingArcX_ne_crossingArcY : crossingArcX ≠ crossingArcY := by
  intro h
  have hmem : ((0 : ℝ), (1 : ℝ)) ∈ crossingArcX := ⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩
  rw [h] at hmem
  exact absurd hmem.2 (by norm_num)

/-- The exchange is not trivial: the two replacement sheets are distinct. -/
theorem spliceArcPos_ne_spliceArcNeg : spliceArcPos ≠ spliceArcNeg := by
  intro h
  exact Set.disjoint_left.mp disjoint_spliceArcPos_spliceArcNeg
    (show ((1 : ℝ), (0 : ℝ)) ∈ spliceArcPos from
      ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩)
    (h ▸ (show ((1 : ℝ), (0 : ℝ)) ∈ spliceArcPos from
      ⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩))

/-- The bottom of the sheet `x = 0` is spliced to the top of the sheet `y = 0`. -/
theorem spliceMk_crossing_bottom_eq_top {a : ℝ × ℝ} (ha : a ∈ crossingArcX) :
    spliceMk (a, 0) = spliceMk (a.swap, 1) ∧ a.swap ∈ crossingArcY :=
  ⟨spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    swap_mem_crossingArcY_of_mem_crossingArcX ha⟩

/-- The bottom of the plane `x - y = 1` is spliced to the top of the plane `x - y = -1`. -/
theorem spliceMk_splice_bottom_eq_top {a : ℝ × ℝ} (ha : a ∈ spliceArcPos) :
    spliceMk (a, 0) = spliceMk (a.swap, 1) ∧ a.swap ∈ spliceArcNeg :=
  ⟨spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    swap_mem_spliceArcNeg_of_mem_spliceArcPos ha⟩

/-! ### The replacement is embedded in the spliced cylinder -/

/-- In the spliced cylinder the two replacement sheets can only meet through the period
identification of their ends. -/
theorem snd_eq_ends_of_spliceMk_eq {p q : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceSheetPos)
    (hq : q ∈ spliceSheetNeg) (h : spliceMk p = spliceMk q) :
    (p.2 = 0 ∧ q.2 = 1) ∨ (p.2 = 1 ∧ q.2 = 0) := by
  rcases spliceMk_eq_iff.mp h with rfl | ⟨h0, h1, -⟩ | ⟨h1, h0, -⟩
  · exact absurd hq (Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg hp)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h1, h0⟩

/-- In the spliced cylinder the two replacement sheets meet exactly in the images of their
two glued end arcs. This is the sense in which the replacement is embedded: it is one surface
closed up across the period, with no interior double point. -/
theorem image_spliceSheetPos_inter_image_spliceSheetNeg :
    spliceMk '' spliceSheetPos ∩ spliceMk '' spliceSheetNeg
      = spliceMk '' (spliceArcPos ×ˢ ({0, 1} : Set ℝ)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨p, hp, rfl⟩, q, hq, hqz⟩
    have hrel : SpliceRel p q := spliceMk_eq_iff.mp hqz.symm
    rcases hrel with rfl | ⟨h0, -, -⟩ | ⟨h1, -, -⟩
    · exact absurd hq (Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg hp)
    · exact ⟨p, ⟨(mem_spliceSheetPos.mp hp).1, Or.inl h0⟩, rfl⟩
    · exact ⟨p, ⟨(mem_spliceSheetPos.mp hp).1, Or.inr h1⟩, rfl⟩
  · rintro z ⟨p, ⟨hpa, hp2⟩, rfl⟩
    have hcases : p.2 = 0 ∨ p.2 = 1 := hp2
    have hp2' : p.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hcases with h | h <;> rw [Set.mem_Icc, h] <;> norm_num
    refine ⟨⟨p, mem_spliceSheetPos.mpr ⟨hpa, hp2'⟩, rfl⟩, ?_⟩
    rcases hcases with h | h
    · refine ⟨(p.1.swap, 1), mem_spliceSheetNeg.mpr
        ⟨swap_mem_spliceArcNeg_of_mem_spliceArcPos hpa, by rw [Set.mem_Icc]; norm_num⟩, ?_⟩
      exact (spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨h, rfl, rfl⟩))).symm
    · refine ⟨(p.1.swap, 0), mem_spliceSheetNeg.mpr
        ⟨swap_mem_spliceArcNeg_of_mem_spliceArcPos hpa, by rw [Set.mem_Icc]; norm_num⟩, ?_⟩
      refine (spliceMk_eq_iff.mpr (Or.inr (Or.inr ⟨h, rfl, ?_⟩))).symm
      exact (Prod.swap_swap p.1).symm

/-! ### Both configurations have the same lateral boundary -/

/-- The arc `x = 0` meets the lateral boundary in the two points `(0, 1)` and `(0, -1)`. -/
theorem crossingArcX_inter_spliceSquareBoundary :
    crossingArcX ∩ spliceSquareBoundary = {((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨-, hx⟩, -, hb⟩
    rcases hb with h | h | h | h
    · rw [hx] at h; norm_num at h
    · rw [hx] at h; norm_num at h
    · exact Or.inr (Prod.ext hx h)
    · exact Or.inl (Prod.ext hx h)
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

/-- The arc `y = 0` meets the lateral boundary in the two points `(1, 0)` and `(-1, 0)`. -/
theorem crossingArcY_inter_spliceSquareBoundary :
    crossingArcY ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((-1 : ℝ), (0 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨-, hy⟩, -, hb⟩
    rcases hb with h | h | h | h
    · exact Or.inr (Prod.ext h hy)
    · exact Or.inl (Prod.ext h hy)
    · rw [hy] at h; norm_num at h
    · rw [hy] at h; norm_num at h
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, rfl⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩

/-- The plane `x - y = 1` meets the lateral boundary in the two points `(1, 0)` and
`(0, -1)`. -/
theorem spliceArcPos_inter_spliceSquareBoundary :
    spliceArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exfalso; rw [h] at hd; linarith [hsq.2.1]
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
    · exfalso; rw [h] at hd; linarith [hsq.1.2]
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

/-- The plane `x - y = -1` meets the lateral boundary in the two points `(-1, 0)` and
`(0, 1)`. -/
theorem spliceArcNeg_inter_spliceSquareBoundary :
    spliceArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨⟨hsq, hd⟩, -, hb⟩
    rw [mem_spliceSquare] at hsq
    rcases hb with h | h | h | h
    · exact Or.inl (Prod.ext h (by linarith [hd, h]))
    · exfalso; rw [h] at hd; linarith [hsq.2.2]
    · exfalso; rw [h] at hd; linarith [hsq.1.1]
    · exact Or.inr (Prod.ext (by linarith [hd, h]) h)
  · rintro (rfl | rfl)
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨⟨by simp only [mem_spliceSquare]; norm_num, by norm_num⟩,
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

/-- The old configuration meets the lateral boundary of the square in the four points
`spliceEnds`. -/
theorem crossingArc_inter_spliceSquareBoundary :
    (crossingArcX ∪ crossingArcY) ∩ spliceSquareBoundary = spliceEnds := by
  rw [Set.union_inter_distrib_right, crossingArcX_inter_spliceSquareBoundary,
    crossingArcY_inter_spliceSquareBoundary]
  ext p
  simp only [spliceEnds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The replacement meets the lateral boundary of the square in the same four points. -/
theorem spliceArc_inter_spliceSquareBoundary :
    (spliceArcPos ∪ spliceArcNeg) ∩ spliceSquareBoundary = spliceEnds := by
  rw [Set.union_inter_distrib_right, spliceArcPos_inter_spliceSquareBoundary,
    spliceArcNeg_inter_spliceSquareBoundary]
  ext p
  simp only [spliceEnds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The old configuration meets the lateral boundary of the cylinder in
`spliceEnds ×ˢ Icc 0 1`. -/
theorem crossingFigure_inter_lateral :
    crossingFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [crossingFigure, Set.prod_inter_prod, Set.inter_self,
    crossingArc_inter_spliceSquareBoundary]

/-- The replacement meets the lateral boundary of the cylinder in `spliceEnds ×ˢ Icc 0 1`. -/
theorem spliceFigure_inter_lateral :
    spliceFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) = spliceEnds ×ˢ Icc (0 : ℝ) 1 := by
  rw [spliceFigure, Set.prod_inter_prod, Set.inter_self, spliceArc_inter_spliceSquareBoundary]

/-- The old configuration and Moise's replacement have literally the same boundary curves in
the ends of the cylinder, which is what lets the replacement be glued in. -/
theorem crossingFigure_inter_lateral_eq_spliceFigure_inter_lateral :
    crossingFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      = spliceFigure ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) := by
  rw [crossingFigure_inter_lateral, spliceFigure_inter_lateral]

/-! ### The boundary is two circles, each double covering the branch -/

/-- The period map has no fixed point among the four lateral boundary points, so a boundary
curve needs two periods to close up. -/
theorem swap_ne_self_of_mem_spliceEnds {a : ℝ × ℝ} (ha : a ∈ spliceEnds) : a.swap ≠ a := by
  simp only [spliceEnds, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

/-- The period map fixes the core of the cylinder, so the branch circle closes up after a
single period. -/
theorem spliceMk_core_zero_eq_one :
    spliceMk (((0 : ℝ), (0 : ℝ)), 0) = spliceMk (((0 : ℝ), (0 : ℝ)), 1) :=
  spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

/-- A lateral boundary point does not close up after a single period: this is the precise
sense in which the single preimage circle doubly covers the branch circle. -/
theorem spliceMk_end_zero_ne_one {a : ℝ × ℝ} (ha : a ∈ spliceEnds) :
    spliceMk (a, (0 : ℝ)) ≠ spliceMk (a, (1 : ℝ)) := by
  intro h
  rcases spliceMk_eq_iff.mp h with h' | ⟨-, -, h'⟩ | ⟨h', -, -⟩
  · exact absurd (congrArg Prod.snd h') (by norm_num)
  · exact swap_ne_self_of_mem_spliceEnds ha h'.symm
  · exact absurd h' (by norm_num)

/-- One period carries the lateral boundary segment over `a` to the one over `a.swap`, so the
two segments over `a` and `a.swap` form a single boundary curve. -/
theorem spliceMk_end_bottom_eq_swap_top (a : ℝ × ℝ) :
    spliceMk (a, (0 : ℝ)) = spliceMk (a.swap, (1 : ℝ)) :=
  spliceMk_eq_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

/-- The upper pair `(0, 1)`, `(1, 0)` and the lower pair `(0, -1)`, `(-1, 0)` of lateral
boundary points stay separate in the spliced cylinder, so the replacement has exactly two
boundary curves, not one and not four. -/
theorem spliceMk_upper_ne_lower {a b : ℝ × ℝ} {s t : ℝ}
    (ha : a ∈ ({((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)))
    (hb : b ∈ ({((0 : ℝ), (-1 : ℝ)), ((-1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))) :
    spliceMk (a, s) ≠ spliceMk (b, t) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  intro h
  rcases spliceMk_eq_iff.mp h with h' | ⟨-, -, h'⟩ | ⟨-, -, h'⟩
  · have h'' : a = b := congrArg Prod.fst h'
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.mk.injEq] at h'' <;> norm_num at h''
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h' <;> norm_num at h'
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h' <;> norm_num at h'

/-! ### Comparison with cylindrical diagrams -/

/-- A cylindrical diagram over the square whose end map is the coordinate swap identifies
exactly the pairs related by `SpliceRel`. So `SpliceRel` is not an ad hoc choice: it is the
identification carried by any piecewise linear realization of the splice.

This is a conditional statement: no realizing diagram is constructed in this file, and none
is claimed to exist. -/
theorem spliceRel_iff_of_isCylindricalDiagram {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (ℝ × ℝ) × ℝ → F} {S : Set F}
    (hf : IsCylindricalDiagram f spliceSquare S)
    (hend : ∀ a ∈ spliceSquare, f (a, 0) = f (a.swap, 1))
    {p q : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) (hq : q ∈ spliceCylinder) :
    f p = f q ↔ SpliceRel p q := by
  have hp1 : p.1 ∈ spliceSquare := (mem_spliceCylinder.mp hp).1
  have hq1 : q.1 ∈ spliceSquare := (mem_spliceCylinder.mp hq).1
  have hpc : p ∈ spliceSquare ×ˢ Icc (0 : ℝ) 1 := hp
  have hqc : q ∈ spliceSquare ×ˢ Icc (0 : ℝ) 1 := hq
  constructor
  · intro h
    rcases hf.eq_or_endpoints p hpc q hqc h with heq | ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exact Or.inl heq
    · refine Or.inr (Or.inl ⟨h0, h1, ?_⟩)
      have hpa : p = (p.1, (0 : ℝ)) := Prod.ext rfl h0
      have hqa : q = (q.1, (1 : ℝ)) := Prod.ext rfl h1
      have e1 : f (p.1.swap, (1 : ℝ)) = f p := by rw [← hend p.1 hp1, ← hpa]
      have e2 : f q = f (q.1, (1 : ℝ)) := by rw [← hqa]
      exact (hf.eq_of_eq_top (swap_mem_spliceSquare hp1) hq1 (e1.trans (h.trans e2))).symm
    · refine Or.inr (Or.inr ⟨h1, h0, ?_⟩)
      have hpa : p = (p.1, (1 : ℝ)) := Prod.ext rfl h1
      have hqa : q = (q.1, (0 : ℝ)) := Prod.ext rfl h0
      have e1 : f (q.1.swap, (1 : ℝ)) = f q := by rw [← hend q.1 hq1, ← hqa]
      have e2 : f p = f (p.1, (1 : ℝ)) := by rw [← hpa]
      exact hf.eq_of_eq_top hp1 (swap_mem_spliceSquare hq1) (e2.symm.trans (h.trans e1.symm))
  · rintro (rfl | ⟨h0, h1, hs⟩ | ⟨h1, h0, hs⟩)
    · rfl
    · have hpa : p = (p.1, (0 : ℝ)) := Prod.ext rfl h0
      have hqa : q = (q.1, (1 : ℝ)) := Prod.ext rfl h1
      have e1 : f p = f (p.1, (0 : ℝ)) := by rw [← hpa]
      have e2 : f q = f (q.1, (1 : ℝ)) := by rw [← hqa]
      rw [e1, e2, hs, hend p.1 hp1]
    · have hpa : p = (p.1, (1 : ℝ)) := Prod.ext rfl h1
      have hqa : q = (q.1, (0 : ℝ)) := Prod.ext rfl h0
      have e1 : f p = f (p.1, (1 : ℝ)) := by rw [← hpa]
      have e2 : f q = f (q.1, (0 : ℝ)) := by rw [← hqa]
      rw [e1, e2, hs, hend q.1 hq1]

end DifferentialGeometry.Topology.PiecewiseLinear
