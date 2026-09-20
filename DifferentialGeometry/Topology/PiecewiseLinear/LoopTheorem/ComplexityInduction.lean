/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchDescent

/-!
# The complexity induction of Moise's Lemma 2

`NormalSingularCellData.DescendingSurgery` is the single step of Moise's Lemma 2: a
replacement normal singular two cell over the same boundary data whose singular set has
strictly smaller `NormalSingularSetTriangulation.complexity`.  The selection files produce
one such step, together with a boundary curve of the replacement that still avoids the fixed
normal subgroup.  Nothing so far iterates that step.  This file is the iteration, and nothing
else: no geometry is proved here.

## What the induction consumes

The step is taken as the hypothesis `step` below, in *exactly* the shape the boundary case
assembly `NormalSingularCellData.exists_descendingSurgery_of_crossSeamTube_reversing`
concludes for a fixed cell, namely

```
∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
  (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N
```

so that assembly plugs in with no adapter once its own open hypotheses are discharged.  The
ambient loop space `X`, the inclusion `ρ`, the basepoint `x` and the normal subgroup `N` are
fixed throughout the induction, as they are in the assembly; only the cell varies.

The induction itself is proved once, for an arbitrary invariant, in
`exists_complexity_eq_zero_of_descendingSurgery_of_motive`; the boundary curve condition is
the instance of it that the assembly supplies, and a producer preserving further invariants
can use the general form instead of repeating the argument.

## The choice of triangulation is not assumed away

`complexity` is a field of the *singular set triangulation*, which is itself a field of a
`NormalSingularCellData`, so a priori it depends on the chosen normality data and not only on
the underlying cell.  Nothing in the tree proves that two normality data for the same cell
have the same complexity, and nothing here assumes it: the induction is on the natural number
`hD.singularSet.complexity` with the statement universally quantified over *pairs* of a cell
and a normality datum for it, and both `step` and the conclusion quantify over such pairs.
The descent used is the field `DescendingSurgery.complexity_lt`, which compares the surgery's
own normality datum with the given one, so no comparison across different data is needed.

## What comes out, and what does not

The conclusion is a normal singular two cell of complexity zero whose boundary curve still
avoids `N`.  Complexity zero is `SingularTwoCell.IsNonsingular`, that is, injectivity on the
source disk, by `NormalSingularCellData.complexity_eq_zero_iff`; the double point set is then
empty by `doublePointSet_eq_empty_iff_injOn`.  Both halves of that bridge are already in
`LoopTheorem.NormalCell`; `doublePointSet_eq_empty_of_complexity_eq_zero` only records their
composite, which was not stated anywhere.

The conclusion is **not** a `NormalSystem.NonsingularCell`.  That structure is attached to a
`NormalSystem` over a normed space and carries a simplicial source complex, a vertex map, a
basepoint connector and a conjugacy class condition; an injective `SingularTwoCell` over a
charted space carries none of these, and no declaration in the tree converts one into the
other.  Producing that conversion, and the general position input that makes the tower's
singular disk normal in the first place, are the two obligations that remain between this
file and `LemmaTwoStatement`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

/-- A singular set of nonzero complexity has a branch to cut at.  The induction step below is
keyed on `complexity ≠ 0`, while every geometric producer of a surgery needs a branch; this is
the passage between the two. -/
theorem nonempty_branch_of_complexity_ne_zero (T : NormalSingularSetTriangulation D BdM)
    (h : T.complexity ≠ 0) : Nonempty T.Branch := by
  rw [← not_isEmpty_iff]
  intro hempty
  let _ : Finite T.Branch := T.finite_branch
  have hclosed : T.closedBranchCount = 0 :=
    Finite.card_eq_zero_iff.mpr (Subtype.isEmpty_of_false fun c _ => hempty.false c)
  have hboundary : T.boundaryBranchCount = 0 :=
    Finite.card_eq_zero_iff.mpr (Subtype.isEmpty_of_false fun c _ => hempty.false c)
  exact h (Nat.add_eq_zero_iff.mpr ⟨hclosed, hboundary⟩)

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- The endpoint of the complexity bridge: a normal singular two cell whose singular set has
complexity zero has no double points at all.  The two halves,
`NormalSingularCellData.complexity_eq_zero_iff` and `doublePointSet_eq_empty_iff_injOn`, are
proved in `LoopTheorem.NormalCell`. -/
theorem doublePointSet_eq_empty_of_complexity_eq_zero (hD : NormalSingularCellData D BdM B)
    (h : hD.singularSet.complexity = 0) : doublePointSet D D.domain = ∅ :=
  (doublePointSet_eq_empty_iff_injOn D D.domain).mpr (hD.complexity_eq_zero_iff.mp h)

/-- **The complexity induction of Moise's Lemma 2, over an arbitrary invariant.**  A surgery
step that preserves `motive` and is available at every cell of nonzero complexity carries
`motive` down to a cell of complexity zero, which is then injective on its source disk and has
empty double point set.

The invariant is quantified over pairs of a cell and a normality datum for it, because the
complexity lives on the datum; a surgery is compared only with the datum it was built from, so
no independence of the complexity from that choice is used.  Taking `motive` to be the
existence of a boundary parametrisation avoiding a normal subgroup recovers
`NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery`; any further invariant
a surgery producer happens to preserve is threaded through without redoing the induction. -/
theorem exists_complexity_eq_zero_of_descendingSurgery_of_motive
    (motive : ∀ D₀ : SingularTwoCell M, NormalSingularCellData D₀ BdM B → Prop)
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 → motive D₀ hD₀ →
      ∃ S : hD₀.DescendingSurgery, motive S.cell S.normal)
    (hD : NormalSingularCellData D BdM B) (hmotive : motive D hD) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
      doublePointSet D' D'.domain = ∅ ∧ motive D' hD' := by
  have key : ∀ n : ℕ, ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity = n → motive D₀ hD₀ →
      ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
        hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
        doublePointSet D' D'.domain = ∅ ∧ motive D' hD' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
      intro D₀ hD₀ hn hD₀motive
      by_cases hzero : hD₀.singularSet.complexity = 0
      · exact ⟨D₀, hD₀, hzero, hD₀.complexity_eq_zero_iff.mp hzero,
          hD₀.doublePointSet_eq_empty_of_complexity_eq_zero hzero, hD₀motive⟩
      · obtain ⟨S, hS⟩ := step D₀ hD₀ hzero hD₀motive
        refine inductionHypothesis S.normal.singularSet.complexity ?_ S.cell S.normal rfl hS
        rw [← hn]
        exact S.complexity_lt
  exact key hD.singularSet.complexity D hD rfl hmotive

/-- **The complexity induction of Moise's Lemma 2.**  Suppose that every normal singular two
cell over the boundary data `BdM`, `B` whose singular set is not already empty, and whose
boundary circle is carried by `ρ` to a free loop of `X` avoiding `N`, admits a descending
surgery whose own boundary circle again avoids `N`.  Then every such cell can be improved, in
finitely many steps, to one of complexity zero whose boundary circle still avoids `N`.

The hypothesis `step` is stated exactly as the boundary case assembly concludes, so that
assembly is its intended instance; it is an open obligation, not a construction, and this file
proves nothing about it.  The induction is on the complexity of the *given* normality datum,
and both `step` and the conclusion range over pairs of a cell and a normality datum for it, so
no independence of the complexity from that choice is used. -/
theorem exists_complexity_eq_zero_of_descendingSurgery {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 →
      (∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N) →
      ∃ (S : hD₀.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain)
        (δ : freeLoop X), (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N)
    (hD : NormalSingularCellData D BdM B)
    (hloop : ∃ (e : loopCircle ≃ₜ frontier D.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = D (e θ)) ∧ ¬loopClassMeets δ x N) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧
      ∃ (e : loopCircle ≃ₜ frontier D'.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D' (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨D', hD', hzero, -, -, hD'loop⟩ :=
    exists_complexity_eq_zero_of_descendingSurgery_of_motive
      (fun D₀ _ => ∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N)
      (fun D₀ hD₀ hne hD₀loop => by
        obtain ⟨S, e, δ, hδ, hδN⟩ := step D₀ hD₀ hne hD₀loop
        exact ⟨S, e, δ, hδ, hδN⟩)
      hD hloop
  exact ⟨D', hD', hzero, hD'loop⟩

/-- **The complexity induction, read through the bridge.**  Same hypotheses as
`NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery`, with the conclusion
spelled out geometrically as well: the improved cell is injective on its source disk and has
empty double point set, and its boundary circle still avoids `N`.

This is the strongest statement layer two of Moise's Lemma 2 can carry.  Turning the improved
cell into a `NormalSystem.NonsingularCell`, and hence into a `NormalSystem.EmbeddedDisk`
through `NonsingularCell.embeddedDisk`, needs data this statement does not have; see the
module docstring. -/
theorem exists_isNonsingular_of_descendingSurgery {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    (step : ∀ (D₀ : SingularTwoCell M) (hD₀ : NormalSingularCellData D₀ BdM B),
      hD₀.singularSet.complexity ≠ 0 →
      (∃ (e : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D₀ (e θ)) ∧ ¬loopClassMeets δ x N) →
      ∃ (S : hD₀.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain)
        (δ : freeLoop X), (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N)
    (hD : NormalSingularCellData D BdM B)
    (hloop : ∃ (e : loopCircle ≃ₜ frontier D.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = D (e θ)) ∧ ¬loopClassMeets δ x N) :
    ∃ (D' : SingularTwoCell M) (hD' : NormalSingularCellData D' BdM B),
      hD'.singularSet.complexity = 0 ∧ D'.IsNonsingular ∧
      doublePointSet D' D'.domain = ∅ ∧
      ∃ (e : loopCircle ≃ₜ frontier D'.domain) (δ : freeLoop X),
        (∀ θ, ρ (δ θ) = D' (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨D', hD', hzero, hD'loop⟩ :=
    exists_complexity_eq_zero_of_descendingSurgery step hD hloop
  exact ⟨D', hD', hzero, hD'.complexity_eq_zero_iff.mp hzero,
    hD'.doublePointSet_eq_empty_of_complexity_eq_zero hzero, hD'loop⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
