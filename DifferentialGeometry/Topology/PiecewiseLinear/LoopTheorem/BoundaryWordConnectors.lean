/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordElimination
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CutAndPaste

/-!
# Basepoint connectors for the boundary word elimination

`BoundaryWordElimination` proves the two candidate elimination identities over an arbitrary
group and records one limitation: geometrically the four letters are paths, not loops at a
single basepoint, so a consumer has to supply the group elements obtained after conjugating
each factor by a connector to the basepoint.  This file supplies that bridge.

## The connector

Moise's cut produces four arcs `σ`, `τ`, `υ`, `φ` closing up to the boundary loop
`σ.trans (τ.trans (υ.trans φ))`.  In the endpoint reversing case (case 3) the arcs have types
`σ υ : Path a b` and `τ φ : Path b a`; in the endpoint preserving case (case 4) they have
types `σ : Path a b`, `τ : Path b b`, `υ : Path b a` and `φ : Path a a`.  Choosing a connector
`c : Path a b` inside the boundary neighbourhood turns the four factors into loops at `a`:

* case 3: `σ.trans c.symm`, `c.trans τ`, `υ.trans c.symm`, `c.trans φ`;
* case 4: `σ.trans c.symm`, `c.trans (τ.trans c.symm)`, `c.trans υ`, `φ`.

In case 4 the fourth factor is already a loop at `a` and needs no connector, while the second
is conjugated on both sides.  Their classes in `FundamentalGroup X a` are the four elements
written `σ̂`, `τ̂`, `ν̂`, `φ̂` below; the corresponding elements of the fundamental group at a
remote basepoint `x` are their images under the multiplicative equivalence
`fundamentalGroupChangeBasepoint q` attached to a connector `q : Path x a`, so every identity
below transports to `x` by `map_mul` and `map_inv`.

## Order reversal

Mathlib's fundamental group multiplies by traversing the right factor first, `g * h = h ⬝ g`.
The four letters of `BoundaryWordElimination` are therefore *not* instantiated at `σ̂`, `τ̂`,
`ν̂`, `φ̂` but at their inverses: with `σ := σ̂⁻¹`, `τ := τ̂⁻¹`, `ν := ν̂⁻¹`, `φ := φ̂⁻¹` the
abstract word `σ * τ * ν * φ` is the inverse of the class of `σ.trans (τ.trans (υ.trans φ))`,
and each abstract candidate word is the inverse of the class of the corresponding candidate
loop.  Instantiating at `σ̂`, `τ̂`, `ν̂`, `φ̂` directly would describe the reversed loops
instead.  Since a normal subgroup is closed under inversion, the elimination statements are
unaffected by the three inversions.

## Main results

* `basedPathClass_boundaryWord_caseThree`, `basedPathClass_firstCandidate_caseThree`,
  `basedPathClass_secondCandidate_caseThree` and their case 4 counterparts: the reduction
  lemmas, expressing the class of each concatenated boundary loop as a word in the four
  connector classes.
* `basedPathClass_boundaryWord_mem_of_caseThree_mem` and
  `basedPathClass_boundaryWord_mem_of_caseFour_mem`: the bridged elimination in
  `FundamentalGroup X a`, obtained from `BoundaryWordElimination` by the substitution above.
  They take the arcs themselves, with no connector argument: the conclusion does not depend on
  the connector, so `σ` is used as one.
* `loopClassMeets_boundaryWord_of_caseThree` and `loopClassMeets_boundaryWord_of_caseFour`:
  the same statements for the free loop classes and the avoidance predicate `loopClassMeets`
  carried by `NormalSystem`, at an arbitrary basepoint of a path connected space.

The contrapositive dichotomy at the level of `loopClassMeets` is already available as
`not_loopClassMeets_or_not_loopClassMeets_of_endpoint_reversing_reconnection` and
`not_loopClassMeets_or_not_loopClassMeets_of_endpoint_preserving_reconnection` in
`LoopTheorem.CutAndPaste`, proved from the order reversed group lemmas of that file; it is not
repeated here.
-/

open CategoryTheory

namespace DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordConnectors

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The fundamental groupoid arrow represented by a path. -/
def pathArrow {a b : X} (p : Path a b) :
    FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  Path.Homotopic.Quotient.mk p

/-- The element of `FundamentalGroup X a` represented by a loop `p : Path a a`. -/
def basedPathClass {a : X} (p : Path a a) : FundamentalGroup X a :=
  pathArrow p

/-- Case 3 reduction lemma for the original boundary word.  With the endpoint reversing arc
types `σ υ : Path a b` and `τ φ : Path b a` and a connector `c : Path a b`, the class of the
boundary loop `σ.trans (τ.trans (υ.trans φ))` is the product `φ̂ * ν̂ * τ̂ * σ̂` of the four
connector classes, the reversed spelling of the word `σ τ ν φ`. -/
theorem basedPathClass_boundaryWord_caseThree {a b : X} (c σ υ : Path a b) (τ φ : Path b a) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) =
      basedPathClass (c.trans φ) * basedPathClass (υ.trans c.symm) *
        basedPathClass (c.trans τ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow τ ≫ (pathArrow υ ≫ pathArrow φ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫ pathArrow τ) ≫
      ((pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow φ)))
  simp

/-- Case 3 reduction lemma for the first candidate boundary word.  The class of
`σ.trans υ.symm` is `ν̂⁻¹ * σ̂`, the reversed spelling of the word `σ ν⁻¹`. -/
theorem basedPathClass_firstCandidate_caseThree {a b : X} (c σ υ : Path a b) :
    basedPathClass (σ.trans υ.symm) =
      (basedPathClass (υ.trans c.symm))⁻¹ * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow υ) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      CategoryTheory.Groupoid.inv
        (pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c))
  simp

/-- Case 3 reduction lemma for the second candidate boundary word.  The class of
`σ.trans (φ.trans (υ.trans τ))` is `τ̂ * ν̂ * φ̂ * σ̂`, the reversed spelling of the word
`σ φ ν τ`. -/
theorem basedPathClass_secondCandidate_caseThree {a b : X} (c σ υ : Path a b)
    (τ φ : Path b a) :
    basedPathClass (σ.trans (φ.trans (υ.trans τ))) =
      basedPathClass (c.trans τ) * basedPathClass (υ.trans c.symm) *
        basedPathClass (c.trans φ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow φ ≫ (pathArrow υ ≫ pathArrow τ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫ pathArrow φ) ≫
      ((pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow τ)))
  simp

/-- Case 4 reduction lemma for the original boundary word.  With the endpoint preserving arc
types `σ : Path a b`, `τ : Path b b`, `υ : Path b a`, `φ : Path a a` and a connector
`c : Path a b`, the class of `σ.trans (τ.trans (υ.trans φ))` is `φ̂ * ν̂ * τ̂ * σ̂`, the reversed
spelling of the word `σ τ ν φ`. -/
theorem basedPathClass_boundaryWord_caseFour {a b : X} (c σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) =
      basedPathClass φ * basedPathClass (c.trans υ) *
        basedPathClass (c.trans (τ.trans c.symm)) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (pathArrow τ ≫ (pathArrow υ ≫ pathArrow φ))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      ((pathArrow c ≫
        (pathArrow τ ≫ CategoryTheory.Groupoid.inv (pathArrow c))) ≫
      ((pathArrow c ≫ pathArrow υ) ≫ pathArrow φ))
  simp

/-- Case 4 reduction lemma for the first candidate boundary word.  The class of `σ.trans υ` is
`ν̂ * σ̂`, the reversed spelling of the word `σ ν`. -/
theorem basedPathClass_firstCandidate_caseFour {a b : X} (c σ : Path a b) (υ : Path b a) :
    basedPathClass (σ.trans υ) =
      basedPathClass (c.trans υ) * basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change pathArrow σ ≫ pathArrow υ =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (pathArrow c ≫ pathArrow υ)
  simp

/-- Case 4 reduction lemma for the second candidate boundary word.  The class of
`σ.trans (τ.symm.trans (υ.trans φ.symm))` is `φ̂⁻¹ * ν̂ * τ̂⁻¹ * σ̂`, the reversed spelling of
the word `σ τ⁻¹ ν φ⁻¹`. -/
theorem basedPathClass_secondCandidate_caseFour {a b : X} (c σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) :
    basedPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm))) =
      (basedPathClass φ)⁻¹ * basedPathClass (c.trans υ) *
        (basedPathClass (c.trans (τ.trans c.symm)))⁻¹ *
        basedPathClass (σ.trans c.symm) := by
  unfold basedPathClass pathArrow
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change (pathArrow σ ≫ (CategoryTheory.Groupoid.inv (pathArrow τ) ≫
      (pathArrow υ ≫ CategoryTheory.Groupoid.inv (pathArrow φ)))) =
    (pathArrow σ ≫ CategoryTheory.Groupoid.inv (pathArrow c)) ≫
      (CategoryTheory.Groupoid.inv
        (pathArrow c ≫ (pathArrow τ ≫ CategoryTheory.Groupoid.inv (pathArrow c))) ≫
      ((pathArrow c ≫ pathArrow υ) ≫ CategoryTheory.Groupoid.inv (pathArrow φ)))
  simp

/-- The bridged case 3 elimination in `FundamentalGroup X a`.  If the classes of the two
candidate boundary loops `σ.trans υ.symm` and `σ.trans (φ.trans (υ.trans τ))` produced by an
endpoint reversing cut lie in the normal subgroup `N`, then so does the class of the original
boundary loop `σ.trans (τ.trans (υ.trans φ))`.  The proof instantiates
`BoundaryWordElimination.boundaryWord_mem_of_caseThree_mem` at the inverses of the four
connector classes, the connector being `σ` itself. -/
theorem basedPathClass_boundaryWord_mem_of_caseThree_mem {a b : X}
    {N : Subgroup (FundamentalGroup X a)} [N.Normal] (σ υ : Path a b) (τ φ : Path b a)
    (h₁ : basedPathClass (σ.trans υ.symm) ∈ N)
    (h₂ : basedPathClass (σ.trans (φ.trans (υ.trans τ))) ∈ N) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) ∈ N := by
  rw [basedPathClass_firstCandidate_caseThree σ σ υ] at h₁
  rw [basedPathClass_secondCandidate_caseThree σ σ υ τ φ] at h₂
  rw [basedPathClass_boundaryWord_caseThree σ σ υ τ φ]
  set S := basedPathClass (σ.trans σ.symm)
  set T := basedPathClass (σ.trans τ)
  set U := basedPathClass (υ.trans σ.symm)
  set P := basedPathClass (σ.trans φ)
  have k₁ : S⁻¹ * (U⁻¹)⁻¹ ∈ N := by
    have h := N.inv_mem h₁
    rwa [show (U⁻¹ * S)⁻¹ = S⁻¹ * (U⁻¹)⁻¹ by group] at h
  have k₂ : S⁻¹ * P⁻¹ * U⁻¹ * T⁻¹ ∈ N := by
    have h := N.inv_mem h₂
    rwa [show (T * U * P * S)⁻¹ = S⁻¹ * P⁻¹ * U⁻¹ * T⁻¹ by group] at h
  have key : S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹ ∈ N :=
    BoundaryWordElimination.boundaryWord_mem_of_caseThree_mem k₁ k₂
  have h := N.inv_mem key
  rwa [show (S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹)⁻¹ = P * U * T * S by group] at h

/-- The bridged case 4 elimination in `FundamentalGroup X a`.  If the classes of the two
candidate boundary loops `σ.trans υ` and `σ.trans (τ.symm.trans (υ.trans φ.symm))` produced by
an endpoint preserving cut lie in the normal subgroup `N`, then so does the class of the
original boundary loop `σ.trans (τ.trans (υ.trans φ))`.  The proof instantiates
`BoundaryWordElimination.boundaryWord_mem_of_caseFour_mem` at the inverses of the four
connector classes, the connector being `σ` itself. -/
theorem basedPathClass_boundaryWord_mem_of_caseFour_mem {a b : X}
    {N : Subgroup (FundamentalGroup X a)} [N.Normal] (σ : Path a b) (τ : Path b b)
    (υ : Path b a) (φ : Path a a) (h₁ : basedPathClass (σ.trans υ) ∈ N)
    (h₂ : basedPathClass (σ.trans (τ.symm.trans (υ.trans φ.symm))) ∈ N) :
    basedPathClass (σ.trans (τ.trans (υ.trans φ))) ∈ N := by
  rw [basedPathClass_firstCandidate_caseFour σ σ υ] at h₁
  rw [basedPathClass_secondCandidate_caseFour σ σ τ υ φ] at h₂
  rw [basedPathClass_boundaryWord_caseFour σ σ τ υ φ]
  set S := basedPathClass (σ.trans σ.symm)
  set T := basedPathClass (σ.trans (τ.trans σ.symm))
  set U := basedPathClass (σ.trans υ)
  set P := basedPathClass φ
  have k₁ : S⁻¹ * U⁻¹ ∈ N := by
    have h := N.inv_mem h₁
    rwa [show (U * S)⁻¹ = S⁻¹ * U⁻¹ by group] at h
  have k₂ : S⁻¹ * (T⁻¹)⁻¹ * U⁻¹ * (P⁻¹)⁻¹ ∈ N := by
    have h := N.inv_mem h₂
    rwa [show (P⁻¹ * U * T⁻¹ * S)⁻¹ = S⁻¹ * (T⁻¹)⁻¹ * U⁻¹ * (P⁻¹)⁻¹ by group] at h
  have key : S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹ ∈ N :=
    BoundaryWordElimination.boundaryWord_mem_of_caseFour_mem k₁ k₂
  have h := N.inv_mem key
  rwa [show (S⁻¹ * T⁻¹ * U⁻¹ * P⁻¹)⁻¹ = P * U * T * S by group] at h

/-- Transport of membership in a normal subgroup of `FundamentalGroup X x` to the fundamental
group at the endpoint of a connector `q : Path x a`: the free loop class of `pathToCircle p`
meets `N` exactly when the connector class of `p` lies in the pullback of `N`. -/
theorem loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap [PathConnectedSpace X]
    {x a : X} (q : Path x a) (N : Subgroup (FundamentalGroup X x)) [N.Normal] (p : Path a a) :
    loopClassMeets (pathToCircle p) x N ↔
      basedPathClass p ∈
        N.comap (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom := by
  have hiff := loopRepresentativeAlong_mem_iff_loopClassMeets_basedCircle q
    (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop a) N
  rw [loopRepresentativeAlong_pathToCircle q p] at hiff
  exact hiff.symm

/-- The bridged case 3 elimination for free loop classes.  If both candidate boundary loops
produced by an endpoint reversing cut have free homotopy classes meeting the normal subgroup
`N` of `FundamentalGroup X x`, then so does the original boundary loop.  No connector appears
in the statement: the conclusion is independent of the choices, and path connectedness supplies
the connector to the basepoint. -/
theorem loopClassMeets_boundaryWord_of_caseThree [PathConnectedSpace X] {x a b : X}
    (σ υ : Path a b) (τ φ : Path b a) (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (h₁ : loopClassMeets (pathToCircle (σ.trans υ.symm)) x N)
    (h₂ : loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) x N) :
    loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N := by
  have q : Path x a := PathConnectedSpace.somePath x a
  have : (N.comap
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom).Normal :=
    ‹N.Normal›.comap _
  refine (loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mpr ?_
  exact basedPathClass_boundaryWord_mem_of_caseThree_mem σ υ τ φ
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₁)
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₂)

/-- The bridged case 4 elimination for free loop classes.  If both candidate boundary loops
produced by an endpoint preserving cut have free homotopy classes meeting the normal subgroup
`N` of `FundamentalGroup X x`, then so does the original boundary loop.  No connector appears
in the statement: the conclusion is independent of the choices, and path connectedness supplies
the connector to the basepoint. -/
theorem loopClassMeets_boundaryWord_of_caseFour [PathConnectedSpace X] {x a b : X}
    (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a)
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (h₁ : loopClassMeets (pathToCircle (σ.trans υ)) x N)
    (h₂ : loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) x N) :
    loopClassMeets (pathToCircle (σ.trans (τ.trans (υ.trans φ)))) x N := by
  have q : Path x a := PathConnectedSpace.somePath x a
  have : (N.comap
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q).toMonoidHom).Normal :=
    ‹N.Normal›.comap _
  refine (loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mpr ?_
  exact basedPathClass_boundaryWord_mem_of_caseFour_mem σ τ υ φ
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₁)
    ((loopClassMeets_pathToCircle_iff_basedPathClass_mem_comap q N _).mp h₂)

end DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordConnectors
