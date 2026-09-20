/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordFourArcs
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

/-!
# Boundary branch descent: selecting between the two Lemma 2 candidates

Moise's Lemma 2 runs an induction on the branch complexity of the singular set of a normal
singular two cell `D`.  Cutting at a *boundary* branch `c` produces two candidate replacement
cells, and the induction step has to produce one candidate that simultaneously

* is again a normal singular two cell over the same boundary data, with a strictly smaller
  `NormalSingularSetTriangulation.complexity`, and
* has a boundary curve whose free homotopy class still avoids the fixed normal subgroup.

Neither requirement selects a candidate on its own.  Both candidates descend, while the word
elimination of `LoopTheorem.BoundaryWordElimination` only says that *at least one of the two*
avoids the normal subgroup, and does not say which.  This file is that selection step.

## The common shape

`NormalSingularCellData.DescendingSurgery` is the shape both candidates are made to reach: a
replacement cell, its normality over the same boundary data, and the strict complexity drop.
Both candidates enter it through the *same* door,
`NormalSingularCellData.DescendingSurgery.ofBranchEquiv`, which turns a bijection between the
branches of the replacement and the branches of `D` other than `c` into the descent through
`NormalSingularSetTriangulation.complexity_lt_of_branchEquiv_compl`.  For the cross reglued
candidate that bijection is the field `CrossSeamResolutionData.branchEquiv`, so
`CrossSeamResolutionData.toDescendingSurgery` is unconditional; the raw cross reglue of
`NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` does not delete the
branch by itself and is not used here.

The common shape deliberately forgets the facts that are specific to one candidate.  Nothing
is lost: `CrossSeamResolutionData.toDescendingSurgery_cell` and
`NormalSingularCellData.DescendingSurgery.ofBranchEquiv_cell` are definitional, so every such
fact can still be stated about `DescendingSurgery.cell`.  The two that matter are kept
explicitly, in `CrossSeamResolutionData.toDescendingSurgery_spec` for the cross candidate and
in `NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch` for the direct
one, whose image control `G '' G.domain ⊆ D '' D.domain` is strictly stronger than the cross
candidate's `cell '' cell.domain ⊆ D '' D.domain ∪ U`.

## Multiplication order

The word elimination is instantiated here through
`not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing` and its endpoint
preserving companion, that is, through the *free loop* form of the dichotomy.  Mathlib's
`FundamentalGroup` multiplies by traversing the right factor first, `g * h = h ⬝ g`, so the
abstract letters of `BoundaryWordElimination` are instantiated at the *inverses* of the four
connector classes; this is done once and for all inside
`LoopTheorem.CutAndPaste` and is recorded in `LoopTheorem.BoundaryWordConnectors`.  Every
statement below is therefore in the *traversal* convention: `pathToCircle (σ.trans υ.symm)` is
the loop that first traverses `σ` and then traverses `υ` backwards, and the four arc word
`σ.trans (τ.trans (υ.trans φ))` is the boundary of `D` traversed once in that order.  No
inversion is applied at this level.

## Main results

* `NormalSingularCellData.DescendingSurgery`, with `ofBranchEquiv`: the common shape and the
  uniform door into it.
* `CrossSeamResolutionData.toDescendingSurgery`: the cross candidate, repaired by the cross
  seam resolution, lands in the common shape unconditionally.
* `NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch`: the direct
  candidate, reduced from the thirty conjunct conclusion of
  `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` to the five facts the
  selection step uses.  It carries no complexity descent; see below.
* `NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or`: the elimination
  of the disjunction into a single existential, possible exactly because the two candidates now
  have the same conclusion type.
* `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing` and
  `..._preserving`: the selection step itself, in the two relative directions of the cut.

## What is assumed

Two geometric inputs are taken as hypotheses rather than proved.

1. *The branch bookkeeping of the direct surgery.*  The conclusion of
   `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` records that the
   double point set of the replacement is contained in that of `D` and misses the carrier of
   `c`, but not that the remaining branches survive; and a subset of a one dimensional complex
   can have more branches than the complex, so the inclusion alone is not a descent.  What is
   missing is the covering statement that the pullback image of the replacement domain
   exhausts `D.domain` off the deleted strip, from which the bijection required by
   `ofBranchEquiv` follows.  The selection theorems therefore take the bijection itself as the
   argument `ebranch`.
2. *The boundary words of the two candidates.*  Both surgery endpoints parametrise the
   boundary circle of their replacement cell as a concatenation of two paths whose *ranges*
   are named arcs of `frontier D.domain`, and `CrossSeamResolutionData` records no boundary
   parametrisation at all.  Identifying those parametrisations with the four arc words
   `σ.trans υ.symm` and `σ.trans (φ.trans (υ.trans τ))` is a lift of a set level equality to a
   free homotopy, which is not available in this tree.  The selection theorems therefore take
   the two identifications as the arguments `hdirect` and `hcross`, each stated through a map
   `ρ : X → M` that reads a loop of the ambient loop space `X` back in `M`.

Everything downstream of those two inputs is proved.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **The common shape of a Lemma 2 boundary branch surgery.**  A replacement singular two
cell, its normality over the *same* boundary data `BdM`, `B`, and the strict drop of the
branch complexity of the singular set.  This is exactly the amount of information the two
candidates of a boundary branch cut have in common, and exactly what Moise's induction
consumes; the candidate specific facts are recorded separately by the producers. -/
structure DescendingSurgery (hD : NormalSingularCellData D BdM B) where
  /-- The replacement singular two cell. -/
  cell : SingularTwoCell M
  /-- The replacement is again a normal singular two cell over the same boundary data. -/
  normal : NormalSingularCellData cell BdM B
  /-- The singular set of the replacement is strictly simpler than that of `D`. -/
  complexity_lt : normal.singularSet.complexity < hD.singularSet.complexity

namespace DescendingSurgery

/-- **The uniform door into the common shape.**  A normal singular two cell over the same
boundary data whose branches correspond bijectively to the branches of `D` other than `c` is a
descending surgery.  Both candidates of a boundary branch cut are made to descend through this
one lemma, so the descent is literally uniform over them; the bijection, not the inclusion of
double point sets, is what forces the drop, because a proper subset of an arc can split into
two arcs and so raise the branch count. -/
def ofBranchEquiv (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    hD.DescendingSurgery where
  cell := G
  normal := hG
  complexity_lt := hD.singularSet.complexity_lt_of_branchEquiv_compl hG.singularSet e

/-- The cell of `ofBranchEquiv` is the cell it was built from, so every fact about that cell
is still a fact about the descending surgery. -/
theorem ofBranchEquiv_cell (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {G : SingularTwoCell M} (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    (ofBranchEquiv hD hG e).cell = G :=
  rfl

/-- The normal cell data of `ofBranchEquiv` is the data it was built from. -/
theorem ofBranchEquiv_normal (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {G : SingularTwoCell M}
    (hG : NormalSingularCellData G BdM B)
    (e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}) :
    (ofBranchEquiv hD hG e).normal = hG :=
  rfl

end DescendingSurgery

end NormalSingularCellData

/-! ### The cross reglued candidate -/

namespace CrossSeamResolutionData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

/-- **The cross candidate in the common shape.**  The cross seam resolution of the boundary
cross reglue is a descending surgery, through the same door `ofBranchEquiv` as the direct
candidate: its field `branchEquiv` is precisely the bijection that door asks for.  No extra
hypothesis is needed, because the resolution already deletes exactly the branch `c`. -/
def toDescendingSurgery (R : CrossSeamResolutionData hD c U) : hD.DescendingSurgery :=
  NormalSingularCellData.DescendingSurgery.ofBranchEquiv hD R.normal R.branchEquiv

/-- The cell of the descending surgery attached to a cross seam resolution is the resolved
cell itself. -/
theorem toDescendingSurgery_cell (R : CrossSeamResolutionData hD c U) :
    R.toDescendingSurgery.cell = R.cell :=
  rfl

/-- The two facts that the common shape forgets on the cross side, kept here: the resolved
cell deletes exactly the carrier of `c` from the double point set, and its image stays inside
the image of `D` together with the resolving tube `U`.  The second is strictly weaker than the
image control of the direct candidate, which needs no tube. -/
theorem toDescendingSurgery_spec (R : CrossSeamResolutionData hD c U) :
    doublePointSet R.toDescendingSurgery.cell R.toDescendingSurgery.cell.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier c ∧
      R.toDescendingSurgery.cell '' R.toDescendingSurgery.cell.domain ⊆ D '' D.domain ∪ U :=
  ⟨R.doublePointSet_eq, R.image_subset⟩

end CrossSeamResolutionData

/-! ### The direct candidate -/

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **The direct boundary surgery candidate, reduced to what the selection step uses.**  The
thirty conjunct conclusion of `exists_boundary_surgery_cell_of_boundaryBranch` is cut down to
the replacement cell, its normality, the two double point facts, the image control, and a
parametrisation of its boundary circle as a concatenation of two paths.

This endpoint carries **no** complexity descent: the recorded conclusion does not say that the
branches of `D` other than `c` survive the surgery, and the inclusion of double point sets is
not by itself a descent.  The image control `G '' G.domain ⊆ D '' D.domain` is the fact that
is strictly stronger on this side than on the cross side. -/
theorem exists_boundary_surgery_candidate_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ G : SingularTwoCell M,
      Nonempty (NormalSingularCellData G BdM B) ∧
        doublePointSet G G.domain ⊆ doublePointSet D D.domain ∧
        Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c) ∧
        G '' G.domain ⊆ D '' D.domain ∧
        ∃ (e : loopCircle ≃ₜ frontier G.domain) (y z : M) (α : Path y z) (ω : Path z y),
          ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, G, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, himage, -, -, -, -, -, -,
    hsub, hdisjoint, -, hG,
    y, z, α, ω, e, -, -, hparam⟩ :=
    hD.exists_boundary_surgery_cell_of_boundaryBranch hc
  exact ⟨G, hG, hsub, hdisjoint, himage, e, y, z, α, ω, hparam⟩

/-! ### Eliminating the disjunction -/

/-- **The selection step, in the abstract.**  Two candidates in the *same* shape, each with a
parametrised boundary curve read in the ambient loop space through `ρ`, and the knowledge that
at least one of the two curves avoids `N`, produce a single descending surgery whose boundary
curve avoids `N`.  This is the only place where the disjunction supplied by the boundary word
elimination is consumed, and it is possible exactly because the two candidates have been made
to have the same conclusion type. -/
theorem exists_descendingSurgery_of_not_loopClassMeets_or
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {δ₁ δ₂ : freeLoop X}
    (e₁ : loopCircle ≃ₜ frontier S₁.cell.domain)
    (e₂ : loopCircle ≃ₜ frontier S₂.cell.domain)
    (h₁ : ∀ θ, ρ (δ₁ θ) = S₁.cell (e₁ θ)) (h₂ : ∀ θ, ρ (δ₂ θ) = S₂.cell (e₂ θ))
    (hdichotomy : ¬loopClassMeets δ₁ x N ∨ ¬loopClassMeets δ₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  rcases hdichotomy with h | h
  · exact ⟨S₁, e₁, δ₁, h₁, h⟩
  · exact ⟨S₂, e₂, δ₂, h₂, h⟩

/-- **The selection step at an endpoint reversing boundary branch cut (Moise's case 3).**  The
four arcs `σ₀`, `τ₀`, `υ₀`, `φ₀` cut the boundary circle of `D` and their images `σ`, `τ`,
`υ`, `φ` in the ambient loop space `X` close up to the boundary curve `γ` of `D`, which avoids
the normal subgroup `N`.  The direct candidate `Gd` traverses `σ.trans υ.symm` and the cross
candidate `R.cell` traverses `σ.trans (φ.trans (υ.trans τ))`.  Both descend, one of the two
avoids `N`, and the conclusion is the single candidate that does both.

The loops are in the traversal convention of the module docstring; the order reversal forced
by `FundamentalGroup` is already absorbed inside
`not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing`.

`ebranch` is the branch bookkeeping of the direct surgery and `hdirect`, `hcross` are the two
boundary word identifications; both are discussed in the module docstring. -/
theorem exists_descendingSurgery_not_loopClassMeets_reversing
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ.symm) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ, ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (δ₁ := pathToCircle (σ.trans υ.symm))
    (δ₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    edirect ecross hdirect hcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

/-- **The selection step at an endpoint preserving boundary branch cut (Moise's case 4).**
The same statement as `exists_descendingSurgery_not_loopClassMeets_reversing` for the other
relative direction of the cut: here the second and the fourth arc are loops, the direct
candidate traverses `σ.trans υ` and the cross candidate traverses
`σ.trans (τ.symm.trans (υ.trans φ.symm))`.

The loops are again in the traversal convention of the module docstring, and `ebranch`,
`hdirect`, `hcross` are again the hypotheses discussed there. -/
theorem exists_descendingSurgery_not_loopClassMeets_preserving
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (ebranch : hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (R : CrossSeamResolutionData hD c U)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (edirect : loopCircle ≃ₜ frontier Gd.domain)
    (hdirect : ∀ θ, ρ (pathToCircle (σ.trans υ) θ) = Gd (edirect θ))
    (ecross : loopCircle ≃ₜ frontier R.cell.domain)
    (hcross : ∀ θ,
      ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))) θ) = R.cell (ecross θ)) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (δ₁ := pathToCircle (σ.trans υ))
    (δ₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    edirect ecross hdirect hcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
