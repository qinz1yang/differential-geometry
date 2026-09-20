/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchDescent

/-!
# Boundary word witnesses

`LoopTheorem.BoundaryBranchDescent` selects between the two Lemma 2 candidates of a boundary
branch cut from two *literal* identifications of their boundary curves with the four arc words,
of the shape

```
hcross : ∀ θ, ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))) θ) = cell (ecross θ)
```

Those selection theorems are correct as conditionals, but this hypothesis cannot be met in the
instantiation it was written for.  With Mathlib's nested `Path.trans`, the four arc word
`w = σ.trans (φ.trans (υ.trans τ))` has `w 0 = σ 0` and `w (3/4) = φ 1`, which is the same
point of `X`; so `w` revisits one point at two distinct circle parameters.  A literal identity
would then force `cell (ecross 0) = cell (ecross (3/4))` with `ecross` injective, that is, a
double point of `cell` lying on its own boundary at that point.  For the resolved cross
candidate that point is an endpoint of the selected branch, which
`CrossSeamResolutionData.doublePointSet_eq` removes from the double point set.  The endpoint
preserving word repeats a point at the parameters `1/2` and `3/4` and is refuted the same way.
`not_exists_realization_of_injOn_frontier` below is that refutation, in the general form in
which it applies to any singular two cell with an injective boundary.

## The replacement

`BoundaryWordWitness` splits the identification in two.  The boundary of the replacement cell
is still parametrised *literally*, by a loop `loop` of the ambient loop space read back through
`ρ`; only the comparison of `loop` with the combinatorial word is relaxed to a free homotopy.
That is the weakest form which still supports the selection step, because the selection consumes
the boundary curve only through `loopClassMeets`, and `loopClassMeets_iff_of_homotopic`
transports `loopClassMeets` across a free homotopy.

## Main results

* `BoundaryWordWitness`: the interface.
* `loopClassMeets_iff_of_homotopic` and `BoundaryWordWitness.loopClassMeets_iff`: the transport.
* `NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or_witness`,
  `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing_witness` and
  `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving_witness`: the
  three selection theorems of `LoopTheorem.BoundaryBranchDescent`, restated on witnesses.  Their
  conclusions are copied unchanged, and the conclusion already has the witness shape — an
  actual parametrised boundary loop together with the avoidance of `N` — so nothing is weakened.
* `NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or_of_realizations`
  and its two companions: the literal statements of `LoopTheorem.BoundaryBranchDescent`, proved
  again here as corollaries of the witness versions through `BoundaryWordWitness.ofRealization`,
  whose homotopy is reflexive.  The literal theorems are therefore consequences of the witness
  ones, and are not orphaned by this file.
* `exists_boundaryWordWitness_not_exists_realization`: non-vacuity.  Over a singular two cell
  with an injective boundary there is a word repeating a value, for which the literal identity
  is impossible and a `BoundaryWordWitness` nevertheless exists.
* `nonempty_boundaryWordWitness_iff_nullhomotopic`: the exact satisfiability criterion when the
  ambient loop space is `M` itself and `ρ` is the identity.  A witness exists for `word` if and
  only if `word` is nullhomotopic; no injectivity of the word is asked for anywhere.

## What this file does not do

It does not build the witness for the resolved cross candidate.  That needs the model boundary
homotopy of the cross seam tube, which is separate work; this file only fixes what that work
has to aim at.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

/-! ### The interface -/

/-- **A boundary word witness.**  The homotopical replacement for a literal identification of
the boundary curve of a singular two cell `G` with a combinatorial word.  The realisation of
the boundary stays literal: `loop` is an honest parametrisation of the boundary circle of `G`,
read in the ambient loop space through `ρ`.  Only the comparison with `word` is up to free
homotopy, which is all the selection step of a Lemma 2 boundary branch cut needs, and which is
what a set level description of the boundary curve can actually supply. -/
structure BoundaryWordWitness {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {X : Type v} [TopologicalSpace X]
    (G : SingularTwoCell M) (ρ : X → M) (word : freeLoop X) where
  /-- A parametrisation of the boundary circle of `G` by the loop circle. -/
  param : loopCircle ≃ₜ frontier G.domain
  /-- A loop of the ambient loop space which traverses that boundary circle. -/
  loop : freeLoop X
  /-- The loop really parametrises the boundary of `G` through `ρ`.  This identity is literal,
  not homotopical. -/
  realizes : ∀ θ, ρ (loop θ) = G (param θ)
  /-- The loop is freely homotopic to the combinatorial word.  Only this comparison is
  relaxed. -/
  homotopic : loop.Homotopic word

/-! ### Transporting the avoidance condition across a free homotopy -/

/-- **Free homotopy preserves the avoidance condition.**  Freely homotopic loops have the same
conjugacy class in the fundamental group, by `FreeLoop.conjugacyClass_eq_of_homotopic`, so one
meets a subgroup exactly when the other does.  Only the forward implication is used by the
selection step below, but the equivalence is the reusable statement. -/
theorem loopClassMeets_iff_of_homotopic {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {γ δ : freeLoop X} (h : γ.Homotopic δ) (x : X)
    (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets γ x N ↔ loopClassMeets δ x N := by
  unfold loopClassMeets
  rw [FreeLoop.conjugacyClass_eq_of_homotopic h x]

namespace BoundaryWordWitness

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}

/-- **A literal identification is a witness.**  The old hypothesis shape of
`LoopTheorem.BoundaryBranchDescent` is the special case of a witness whose homotopy is
reflexive, so every consumer of the witness interface still accepts a literal identity.  The
converse fails; see `exists_boundaryWordWitness_not_exists_realization`. -/
def ofRealization (e : loopCircle ≃ₜ frontier G.domain) (h : ∀ θ, ρ (word θ) = G (e θ)) :
    BoundaryWordWitness G ρ word where
  param := e
  loop := word
  realizes := h
  homotopic := ContinuousMap.Homotopic.refl word

/-- **The transport, at a witness.**  The parametrising loop of a witness meets the subgroup
`N` exactly when the combinatorial word does. -/
theorem loopClassMeets_iff [PathConnectedSpace X] (W : BoundaryWordWitness G ρ word) (x : X)
    (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets W.loop x N ↔ loopClassMeets word x N :=
  loopClassMeets_iff_of_homotopic W.homotopic x N

end BoundaryWordWitness

/-! ### The selection step, restated on witnesses -/

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **The selection step, in the abstract, on witnesses.**  The witness version of
`NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or`: the two candidates
carry boundary word witnesses instead of literal identifications, and the disjunction is read
on the two combinatorial words.  The conclusion is copied unchanged, and is met by the
parametrising loop of the selected witness, which is an honest boundary parametrisation. -/
theorem exists_descendingSurgery_of_not_loopClassMeets_or_witness
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {w₁ w₂ : freeLoop X}
    (W₁ : BoundaryWordWitness S₁.cell ρ w₁) (W₂ : BoundaryWordWitness S₂.cell ρ w₂)
    (hdichotomy : ¬loopClassMeets w₁ x N ∨ ¬loopClassMeets w₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  rcases hdichotomy with h | h
  · exact ⟨S₁, W₁.param, W₁.loop, W₁.realizes, fun hc => h ((W₁.loopClassMeets_iff x N).mp hc)⟩
  · exact ⟨S₂, W₂.param, W₂.loop, W₂.realizes, fun hc => h ((W₂.loopClassMeets_iff x N).mp hc)⟩

/-- **The selection step at an endpoint reversing boundary branch cut, on witnesses.**  The
witness version of `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing`.
Everything except the two boundary word hypotheses is unchanged: the four arcs still cut the
boundary circle of `D`, the boundary curve `γ` still avoids `N`, and `ebranch` is still the
branch bookkeeping of the direct surgery.  What changes is that the direct candidate traverses
a loop *freely homotopic* to `σ.trans υ.symm` and the cross candidate one freely homotopic to
`σ.trans (φ.trans (υ.trans τ))`, rather than being parametrised by those words on the nose. -/
theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness
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
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wcross : BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ.symm))
    (w₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

/-- **The selection step at an endpoint preserving boundary branch cut, on witnesses.**  The
witness version of
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving`, in the other
relative direction of the cut: the second and the fourth arc are loops, the direct candidate
traverses a loop freely homotopic to `σ.trans υ` and the cross candidate one freely homotopic
to `σ.trans (τ.symm.trans (υ.trans φ.symm))`. -/
theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness
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
    {ρ : X → M} (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wcross :
      BoundaryWordWitness R.cell ρ (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  refine exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (S₁ := DescendingSurgery.ofBranchEquiv hD hGd ebranch) (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ))
    (w₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

/-! ### The literal statements, re-derived as corollaries -/

/-- **The literal abstract selection step, as a corollary.**  This is the statement of
`NormalSingularCellData.exists_descendingSurgery_of_not_loopClassMeets_or`, proved here from
the witness version through the reflexive homotopy of `BoundaryWordWitness.ofRealization`.  The
literal theorem is therefore a consequence of the witness one. -/
theorem exists_descendingSurgery_of_not_loopClassMeets_or_of_realizations
    {hD : NormalSingularCellData D BdM B} {X : Type v} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} {N : Subgroup (FundamentalGroup X x)} {ρ : X → M}
    {S₁ S₂ : hD.DescendingSurgery} {δ₁ δ₂ : freeLoop X}
    (e₁ : loopCircle ≃ₜ frontier S₁.cell.domain)
    (e₂ : loopCircle ≃ₜ frontier S₂.cell.domain)
    (h₁ : ∀ θ, ρ (δ₁ θ) = S₁.cell (e₁ θ)) (h₂ : ∀ θ, ρ (δ₂ θ) = S₂.cell (e₂ θ))
    (hdichotomy : ¬loopClassMeets δ₁ x N ∨ ¬loopClassMeets δ₂ x N) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_of_not_loopClassMeets_or_witness
    (BoundaryWordWitness.ofRealization e₁ h₁) (BoundaryWordWitness.ofRealization e₂ h₂)
    hdichotomy

/-- **The literal endpoint reversing selection step, as a corollary.**  This is the statement of
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing`, proved here from
the witness version.  The two literal identifications `hdirect` and `hcross` are turned into
witnesses with a reflexive homotopy, so the committed theorem survives as a proved consequence
of the replacement. -/
theorem exists_descendingSurgery_not_loopClassMeets_reversing_of_realizations
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_reversing_witness hGd ebranch R σ₀ τ₀ υ₀ φ₀ ev
    hev hσ hτ hυ hφ γ hγ hγN (BoundaryWordWitness.ofRealization edirect hdirect)
    (BoundaryWordWitness.ofRealization ecross hcross)

/-- **The literal endpoint preserving selection step, as a corollary.**  This is the statement
of `NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving`, proved here
from the witness version in the same way. -/
theorem exists_descendingSurgery_not_loopClassMeets_preserving_of_realizations
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_preserving_witness hGd ebranch R σ₀ τ₀ υ₀ φ₀ ev
    hev hσ hτ hυ hφ γ hγ hγN (BoundaryWordWitness.ofRealization edirect hdirect)
    (BoundaryWordWitness.ofRealization ecross hcross)

end NormalSingularCellData

/-! ### Non-vacuity -/

section NonVacuity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- The boundary circle of a singular two cell, parametrised by a homeomorphism from the loop
circle and read in the ambient space. -/
def boundaryFreeLoop (G : SingularTwoCell M) (param : loopCircle ≃ₜ frontier G.domain) :
    freeLoop M :=
  G.boundary.comp ⟨fun θ => param θ, param.continuous⟩

@[simp]
theorem boundaryFreeLoop_apply (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) (θ : loopCircle) :
    boundaryFreeLoop G param θ = G (param θ) :=
  rfl

/-- **The honest degenerate witness.**  The boundary loop of a cell is a witness for itself,
with a reflexive homotopy.  This is the configuration in which the literal identity also holds,
and it shows the interface is inhabited without any hypothesis on the cell. -/
def BoundaryWordWitness.ofBoundary (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    BoundaryWordWitness G (id : M → M) (boundaryFreeLoop G param) where
  param := param
  loop := boundaryFreeLoop G param
  realizes := fun _ => rfl
  homotopic := ContinuousMap.Homotopic.refl _

/-- **A repeated value of the word forces a double point on the boundary.**  This is the reason
a literal identification of a boundary curve with a four arc word is unsatisfiable: the word
revisits a point of `X`, and a literal identity transfers that coincidence to the boundary
circle of the cell, where the parametrisation is injective. -/
theorem mem_doublePointSet_of_boundary_realization {X : Type v} [TopologicalSpace X]
    {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}
    (e : loopCircle ≃ₜ frontier G.domain) (h : ∀ θ, ρ (word θ) = G (e θ))
    {θ₁ θ₂ : loopCircle} (hne : θ₁ ≠ θ₂) (hword : word θ₁ = word θ₂) :
    ρ (word θ₁) ∈ doublePointSet G (frontier G.domain) := by
  refine ⟨(e θ₁ : EuclideanSpace ℝ (Fin 2)), (e θ₁).2,
    (e θ₂ : EuclideanSpace ℝ (Fin 2)), (e θ₂).2, ?_, (h θ₁).symm, ?_⟩
  · exact fun hcoe => hne (e.injective (Subtype.ext hcoe))
  · rw [← h θ₂, ← hword]

/-- **The literal identity is impossible once the word repeats a value.**  Over a singular two
cell whose boundary is injective, no homeomorphism of the loop circle onto the boundary circle
can identify it with a word taking the same value at two distinct parameters. -/
theorem not_exists_realization_of_injOn_frontier {X : Type v} [TopologicalSpace X]
    {G : SingularTwoCell M} {ρ : X → M} {word : freeLoop X}
    (hinj : InjOn G (frontier G.domain)) {θ₁ θ₂ : loopCircle} (hne : θ₁ ≠ θ₂)
    (hword : word θ₁ = word θ₂) :
    ¬∃ e : loopCircle ≃ₜ frontier G.domain, ∀ θ, ρ (word θ) = G (e θ) := by
  rintro ⟨e, h⟩
  obtain ⟨p, hp, q, hq, hpq, hfp, hfq⟩ :=
    mem_doublePointSet_of_boundary_realization e h hne hword
  exact hpq (hinj hp hq (hfp.trans hfq.symm))

/-- **The boundary loop of a singular two cell is nullhomotopic.**  It factors through the
domain of the cell, which is a piecewise linear ball and hence contractible. -/
theorem nullhomotopic_boundaryFreeLoop (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) : (boundaryFreeLoop G param).Nullhomotopic := by
  have := G.isPLBall_domain.contractibleSpace
  let d : C(G.domain, M) :=
    ⟨fun y => G y, continuousOn_iff_continuous_domRestrict.mp G.continuousOn⟩
  let pcd : C(loopCircle, G.domain) :=
    ⟨fun θ => ⟨(param θ : EuclideanSpace ℝ (Fin 2)),
        G.frontier_subset_domain (param θ).2⟩,
      (continuous_subtype_val.comp param.continuous).subtype_mk _⟩
  have hpcd : pcd.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic G.domain).comp_left pcd
  have heq : boundaryFreeLoop G param = d.comp pcd := ContinuousMap.ext fun _ => rfl
  rw [heq]
  exact hpcd.comp_right d

/-- **A witness for a constant word.**  The boundary loop of a singular two cell is freely
homotopic to a constant loop, so it is the parametrising loop of a witness whose combinatorial
word is that constant.  A constant word takes the same value at every parameter. -/
theorem exists_boundaryWordWitness_const (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    ∃ y : M,
      Nonempty (BoundaryWordWitness G (id : M → M) (ContinuousMap.const loopCircle y)) := by
  obtain ⟨y, hy⟩ := nullhomotopic_boundaryFreeLoop G param
  exact ⟨y, ⟨⟨param, boundaryFreeLoop G param, fun _ => rfl, hy⟩⟩⟩

/-- **What a witness amounts to over the ambient space itself.**  Take the ambient loop space
to be `M` and `ρ` the identity, which is the canonical instantiation.  A witness for `word`
exists exactly when `word` is nullhomotopic: the parametrising loop of a witness is a boundary
loop of `G`, and a boundary loop of a singular two cell is nullhomotopic because it factors
through the domain ball.  Nothing here asks the word to be injective, so a word repeating a
value is no obstruction at all — which is precisely the failure mode of the literal identity
recorded in `not_exists_realization_of_injOn_frontier`. -/
theorem nonempty_boundaryWordWitness_iff_nullhomotopic [PathConnectedSpace M]
    (G : SingularTwoCell M) (param : loopCircle ≃ₜ frontier G.domain) (word : freeLoop M) :
    Nonempty (BoundaryWordWitness G (id : M → M) word) ↔ word.Nullhomotopic := by
  have hne : Nonempty loopCircle := ⟨0⟩
  constructor
  · rintro ⟨W⟩
    have hloop : W.loop = boundaryFreeLoop G W.param := ContinuousMap.ext fun θ => W.realizes θ
    obtain ⟨y, hy⟩ := nullhomotopic_boundaryFreeLoop G W.param
    have hy' : W.loop.Homotopic (ContinuousMap.const loopCircle y) := by rw [hloop]; exact hy
    exact ⟨y, W.homotopic.symm.trans hy'⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy'⟩ := nullhomotopic_boundaryFreeLoop G param
    have hconst : (ContinuousMap.const loopCircle y').Homotopic
        (ContinuousMap.const loopCircle y) :=
      ContinuousMap.homotopic_const_iff.mpr (PathConnectedSpace.joined y' y)
    exact ⟨⟨param, boundaryFreeLoop G param, fun _ => rfl,
      hy'.trans (hconst.trans hy.symm)⟩⟩

/-- Two distinct points of the loop circle, exhibited so that a constant word can be seen to
repeat a value. -/
theorem loopCircle_zero_ne_half : ((0 : ℝ) : loopCircle) ≠ ((1 / 2 : ℝ) : loopCircle) := by
  intro hcontra
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := Set.mem_Ico.mpr ⟨by norm_num, by norm_num⟩
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hzero hhalf).mp hcontra
  norm_num at this

/-- **Non-vacuity of the witness interface.**  Over any singular two cell with an injective
boundary there is a word which takes the same value at two distinct circle parameters, for
which a `BoundaryWordWitness` exists although the literal identification of the boundary curve
with that word is impossible.  The witness interface is therefore strictly weaker than the
hypothesis it replaces, and is not weaker vacuously: this is the exact configuration in which
the old hypothesis shape could not be met. -/
theorem exists_boundaryWordWitness_not_exists_realization (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) (hinj : InjOn G (frontier G.domain)) :
    ∃ word : freeLoop M,
      (∃ θ₁ θ₂ : loopCircle, θ₁ ≠ θ₂ ∧ word θ₁ = word θ₂) ∧
        Nonempty (BoundaryWordWitness G (id : M → M) word) ∧
        ¬∃ e : loopCircle ≃ₜ frontier G.domain, ∀ θ, (id : M → M) (word θ) = G (e θ) := by
  obtain ⟨y, hW⟩ := exists_boundaryWordWitness_const G param
  refine ⟨ContinuousMap.const loopCircle y,
    ⟨((0 : ℝ) : loopCircle), ((1 / 2 : ℝ) : loopCircle), loopCircle_zero_ne_half, rfl⟩, hW, ?_⟩
  exact not_exists_realization_of_injOn_frontier (ρ := (id : M → M))
    (word := ContinuousMap.const loopCircle y) hinj loopCircle_zero_ne_half rfl

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
