/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell

/-!
# Branch descent for normal singular set triangulations

`DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.complexity` is
the measure that a Lemma 2 surgery has to decrease strictly. This file isolates the purely
combinatorial counting behind such a descent, so that a geometric surgery producer only has
to supply a correspondence between the branches of the old and of the new triangulation.

The load-bearing observation is that the branch type of a normal singular set triangulation
is finite, and that every branch is exactly one of closed or boundary; hence the complexity
is literally the number of branches, `complexity_eq_natCard_branch`. Two consumers follow:

* `complexity_lt_of_injective_origin`, for a surgery that deletes a branch: an injection of
  the new branches into the old ones missing at least one old branch decreases the
  complexity strictly;
* `complexity_add_card_eq_of_equiv_compl` and `complexity_lt_of_card_lt_of_equiv_compl`, for
  a surgery that replaces a finite set of old branches by a finite set of new ones while
  matching the untouched branches bijectively.

A strict inclusion of singular sets is *not* by itself enough for descent: a proper subset
of an arc can be a union of two disjoint subarcs and so raise the branch count. This is why
the counting happens at the level of branches, and why both consumers take the branch
correspondence as a hypothesis rather than deriving it from geometry.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- Splitting a finite type along a predicate splits its cardinality. -/
theorem natCard_subtype_add_natCard_subtype_not {α : Type*} [Finite α] (p : α → Prop) :
    Nat.card {a : α // p a} + Nat.card {a : α // ¬p a} = Nat.card α := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl p)

/-- In a finite type, the elements outside a finite set together with that set account for
every element. -/
theorem natCard_subtype_notMem_add_card {α : Type*} [Finite α] (s : Finset α) :
    Nat.card {a : α // a ∉ s} + s.card = Nat.card α := by
  have hmem : Nat.card {a : α // a ∈ s} = s.card := Nat.card_eq_finsetCard s
  have hsplit := natCard_subtype_add_natCard_subtype_not fun a : α => a ∈ s
  rw [hmem] at hsplit
  omega

/-- An injection into a finite type whose range misses an element strictly decreases
`Nat.card`. -/
theorem natCard_lt_of_injective_of_notMem {α β : Type*} [Finite β] (f : α → β)
    (hf : Function.Injective f) {b : β} (hb : b ∉ Set.range f) :
    Nat.card α < Nat.card β := by
  have _hα : Finite α := Finite.of_injective f hf
  have _iα := Fintype.ofFinite α
  have _iβ := Fintype.ofFinite β
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hf hb

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

/-- The singular set of a normal singular set triangulation is a finite one-dimensional
complex, so it has only finitely many branches. -/
theorem finite_branch (T : NormalSingularSetTriangulation D BdM) : Finite T.Branch := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite T.complex.vertices :=
    (SimplicialComplex.finite_vertices T.complex).to_subtype
  infer_instance

/-- The counting lemma: every branch is exactly one of closed or boundary and there are
only finitely many branches, so the complexity of a normal singular set triangulation is
the number of its branches. -/
theorem complexity_eq_natCard_branch (T : NormalSingularSetTriangulation D BdM) :
    T.complexity = Nat.card T.Branch := by
  let _ : Finite T.Branch := T.finite_branch
  simp only [complexity, closedBranchCount, boundaryBranchCount]
  rw [Nat.add_comm]
  exact natCard_subtype_add_natCard_subtype_not _

/-- Descent for a surgery that deletes a branch. If the branches of `T'` inject into the
branches of `T` and the branch `c` of `T` is not in the image, then the complexity drops
strictly. The correspondence `origin` is a hypothesis: no geometry is used here. -/
theorem complexity_lt_of_injective_origin (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (origin : T'.Branch → T.Branch) (hinj : Function.Injective origin)
    (hmiss : ∀ c', origin c' ≠ c) :
    T'.complexity < T.complexity := by
  let _ : Finite T.Branch := T.finite_branch
  rw [T.complexity_eq_natCard_branch, T'.complexity_eq_natCard_branch]
  refine natCard_lt_of_injective_of_notMem origin hinj (b := c) ?_
  rintro ⟨c', hc'⟩
  exact hmiss c' hc'

/-- Exact bookkeeping for a surgery that replaces the old branches in `O` by the new
branches in `R`. Given a bijection between the branches untouched on either side, the two
complexities differ exactly by the two cardinalities. The bijection is a hypothesis: no
geometry is used here. -/
theorem complexity_add_card_eq_of_equiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (O : Finset T.Branch)
    (R : Finset T'.Branch) (e : {c' : T'.Branch // c' ∉ R} ≃ {c : T.Branch // c ∉ O}) :
    T'.complexity + O.card = T.complexity + R.card := by
  let _ : Finite T.Branch := T.finite_branch
  let _ : Finite T'.Branch := T'.finite_branch
  have hO := natCard_subtype_notMem_add_card O
  have hR := natCard_subtype_notMem_add_card R
  have he : Nat.card {c' : T'.Branch // c' ∉ R} = Nat.card {c : T.Branch // c ∉ O} :=
    Nat.card_congr e
  rw [T.complexity_eq_natCard_branch, T'.complexity_eq_natCard_branch]
  omega

/-- Descent for a replacement surgery: if strictly fewer new branches replace the old
branches in `O`, and the untouched branches correspond bijectively, then the complexity
drops strictly. -/
theorem complexity_lt_of_card_lt_of_equiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (O : Finset T.Branch)
    (R : Finset T'.Branch) (e : {c' : T'.Branch // c' ∉ R} ≃ {c : T.Branch // c ∉ O})
    (hcard : R.card < O.card) :
    T'.complexity < T.complexity := by
  have h := complexity_add_card_eq_of_equiv_compl T T' O R e
  omega

end NormalSingularSetTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
