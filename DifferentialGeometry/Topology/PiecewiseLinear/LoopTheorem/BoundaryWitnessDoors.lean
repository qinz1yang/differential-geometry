/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchInjection

/-!
# Boundary word witnesses through the injection door

Two independent repairs of the boundary branch selection step of Moise's Lemma 2, each
removing a hypothesis shape that the intended instantiation cannot meet.

## The injection door

`LoopTheorem.BoundaryWordWitness` states its two selection theorems with the branch
bookkeeping of the direct candidate given as a *bijection*
`hGd.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}`, that is, through the door
`NormalSingularCellData.DescendingSurgery.ofBranchEquiv`.  The direct boundary surgery does
not supply a bijection: it glues the two outer cells of
`NormalSingularCellData.exists_three_cells_of_boundaryBranch` and discards the interior of the
middle band, losing every branch with a sheet there.  What it does supply is an injection
missing `c`, which is what `NormalSingularSetTriangulation.complexity_lt_of_injective_origin`
needs and what `NormalSingularCellData.DescendingSurgery.ofBranchInjection` turns into a
descending surgery; `NormalSingularCellData.DescendingSurgery.ofBoundarySurgery` is the
producer, and it produces an injection and never a bijection.

`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection`
and its endpoint preserving companion are therefore the same two selection theorems with
`ebranch` replaced by `origin`, `hinj`, `hmiss`.  Nothing else changes: the conclusions are
copied unchanged, and the disjunction still comes from the word elimination of
`BoundaryWordFourArcs`.  The direct witness is accepted where a witness for the cell of the
descending surgery is expected because `ofBranchInjection_cell` is definitional.

The generalisation is conservative: `..._reversing_witness_of_equiv` and
`..._preserving_witness_of_equiv` restate the two bijection versions verbatim and derive them
from the injection versions, so every datum which reached the old door reaches the new one.

## Lifting a manifold valued boundary parametrisation

The second repair concerns the *ambient loop space*.  A witness compares a loop of `X` read in
`M` through `ρ` with a combinatorial word of `X`, while the surgery producers parametrise the
boundary circle of their replacement cell by a word of `M`, as in the last conjunct of
`NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch`.  When `ρ` is an
embedding whose range contains the boundary curve, `BoundaryWordWitness.liftFreeLoop` lifts
that word to `X` — continuity comes from the inducing property, so no section of `ρ` and no
local triviality is needed — and `BoundaryWordWitness.ofManifoldRealization` turns the
manifold valued parametrisation into a witness over the lifted word.

## Main results

* `exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection` and
  `..._preserving_witness_of_injection`, both in the `NormalSingularCellData` namespace: the
  two selection theorems at the injection door.
* `exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_equiv` and
  `..._preserving_witness_of_equiv`: the bijection versions, re-derived.
* `BoundaryWordWitness.liftFreeLoop` and `BoundaryWordWitness.ofManifoldRealization`: the lift
  and the producer.
* `BoundaryWordWitness.exists_of_twoArcParametrization`: the producer applied to the two arc
  parametrisation the direct candidate actually records.
* `exists_boundaryWordWitness_image_subtypeVal` with `range_subtypeVal_image_ne_univ`:
  non-vacuity at an ambient loop space which is a proper subspace of `M`.

## What this file does not do

The two arc word `pathToCircle (α.trans ω)` produced here is *not* the four arc word
`pathToCircle (σ.trans υ.symm)` that the selection theorems consume.  Passing from one to the
other is a separate open problem and nothing below says anything about it.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

/-! ### The selection step at the injection door -/

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **The selection step at an endpoint reversing boundary branch cut, through an injection.**
The statement of
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing_witness` with the
branch bijection `ebranch` replaced by an injection `origin` of the branches of the direct
candidate into the branches of `D` missing `c`.  This is the bookkeeping the direct boundary
surgery really supplies, by `NormalSingularCellData.DescendingSurgery.ofBoundarySurgery`.  The
conclusion is unchanged, and so is everything else: the four arcs still cut the boundary circle
of `D`, the boundary curve `γ` still avoids `N`, and the two candidates still carry boundary
word witnesses. -/
theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (origin : hGd.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c)
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
    (S₁ := DescendingSurgery.ofBranchInjection hD hGd origin hinj hmiss)
    (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ.symm))
    (w₂ := pathToCircle (σ.trans (φ.trans (υ.trans τ))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

/-- **The selection step at an endpoint preserving boundary branch cut, through an injection.**
The endpoint preserving companion of
`exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection`, in the other
relative direction of the cut: the second and the fourth arc are loops, the direct candidate
traverses a loop freely homotopic to `σ.trans υ` and the cross candidate one freely homotopic
to `σ.trans (τ.symm.trans (υ.trans φ.symm))`. -/
theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_injection
    {U : Set M} {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : NormalSingularCellData Gd BdM B)
    (origin : hGd.singularSet.Branch → hD.singularSet.Branch)
    (hinj : Function.Injective origin) (hmiss : ∀ b, origin b ≠ c)
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
    (S₁ := DescendingSurgery.ofBranchInjection hD hGd origin hinj hmiss)
    (S₂ := R.toDescendingSurgery)
    (w₁ := pathToCircle (σ.trans υ))
    (w₂ := pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))
    Wdirect Wcross ?_
  exact not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving σ₀ τ₀ υ₀ φ₀
    ev hev (PathConnectedSpace.somePath x a) (PathConnectedSpace.somePath a b) hσ hτ hυ hφ γ hγ
    N hγN

/-! ### The bijection versions, re-derived -/

/-- **The endpoint reversing selection step at a branch bijection, as a corollary.**  This is
the statement of
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_reversing_witness`, proved
here from the injection version: a bijection onto the branches other than `c` is in particular
an injection missing `c`.  The injection door is therefore reached by every datum the bijection
door was, so no generality is lost and the committed theorem is not orphaned. -/
theorem exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_equiv
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_reversing_witness_of_injection hGd
    (fun b => (ebranch b).1) (Subtype.val_injective.comp ebranch.injective)
    (fun b => (ebranch b).2) R σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

/-- **The endpoint preserving selection step at a branch bijection, as a corollary.**  This is
the statement of
`NormalSingularCellData.exists_descendingSurgery_not_loopClassMeets_preserving_witness`, proved
from the injection version in the same way. -/
theorem exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_equiv
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
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N :=
  exists_descendingSurgery_not_loopClassMeets_preserving_witness_of_injection hGd
    (fun b => (ebranch b).1) (Subtype.val_injective.comp ebranch.injective)
    (fun b => (ebranch b).2) R σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN Wdirect Wcross

end NormalSingularCellData

/-! ### Lifting a manifold valued boundary parametrisation -/

namespace BoundaryWordWitness

section Lift

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {ρ : X → M}

/-- **The lift of a free loop through an embedding.**  A loop of `M` whose values all lie in
the range of an embedding `ρ : X → M` is the image of a loop of `X`.  Only the inducing part of
`hρ` is used, for continuity: a pointwise preimage is chosen by `Classical.choose`, and
`Topology.IsInducing.continuous_iff` promotes the continuity of the composite back to the
continuity of the chosen map.  No section of `ρ` and no local triviality is needed. -/
noncomputable def liftFreeLoop (hρ : IsEmbedding ρ) (w : freeLoop M)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : freeLoop X :=
  ⟨fun θ => Classical.choose (Set.mem_range.mp (hw θ)),
    hρ.isInducing.continuous_iff.mpr <| by
      have hspec : (ρ ∘ fun θ => Classical.choose (Set.mem_range.mp (hw θ))) = ⇑w :=
        funext fun θ => Classical.choose_spec (Set.mem_range.mp (hw θ))
      rw [hspec]
      exact w.continuous⟩

/-- The lifted loop really is a lift: reading it back through `ρ` returns the original loop of
`M`.  This is not a `simp` lemma, because its left-hand side has the variable `ρ` as head
symbol and would match every term. -/
theorem liftFreeLoop_apply (hρ : IsEmbedding ρ) (w : freeLoop M)
    (hw : ∀ θ, w θ ∈ Set.range ρ) (θ : loopCircle) :
    ρ (liftFreeLoop hρ w hw θ) = w θ :=
  Classical.choose_spec (Set.mem_range.mp (hw θ))

end Lift

section Manifold

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

/-- **A manifold valued boundary parametrisation is a witness.**  The surgery producers of
`LoopTheorem.BoundaryBranchDescent` parametrise the boundary circle of their replacement cell
by a loop of `M`, not by a word of the ambient loop space `X`.  When `ρ` is an embedding whose
range contains that loop, the loop lifts to `X` and the parametrisation becomes a boundary word
witness, over the lifted word and with a reflexive homotopy. -/
noncomputable def ofManifoldRealization (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : BoundaryWordWitness G ρ (liftFreeLoop hρ w hw) :=
  ofRealization e fun θ => (liftFreeLoop_apply hρ w hw θ).trans (h θ).symm

/-- The parametrisation of `ofManifoldRealization` is the given boundary parametrisation. -/
@[simp]
theorem ofManifoldRealization_param (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) : (ofManifoldRealization hρ e h hw).param = e :=
  rfl

/-- The parametrising loop of `ofManifoldRealization` is the lift of the given loop of `M`. -/
@[simp]
theorem ofManifoldRealization_loop (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {w : freeLoop M} (h : ∀ θ, G (e θ) = w θ)
    (hw : ∀ θ, w θ ∈ Set.range ρ) :
    (ofManifoldRealization hρ e h hw).loop = liftFreeLoop hρ w hw :=
  rfl

/-- **The producer at the two arc parametrisation of the direct candidate.**  The last
conjunct of `NormalSingularCellData.exists_boundary_surgery_candidate_of_boundaryBranch`
records the boundary circle of the direct replacement cell as the concatenation of two paths
of `M`.  Over an embedding `ρ` whose range contains the boundary curve of the cell, that
parametrisation produces a boundary word witness, whose word reads back through `ρ` as the
same two arc word.

The word obtained here is the *two* arc word.  The four arc word consumed by the selection
theorems is a different loop, and passing from one to the other is not addressed here. -/
theorem exists_of_twoArcParametrization (hρ : IsEmbedding ρ)
    (hrange : Set.range ⇑G.boundary ⊆ Set.range ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {y z : M} (α : Path y z) (ω : Path z y)
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ) :
    ∃ w : freeLoop X, Nonempty (BoundaryWordWitness G ρ w) ∧
      ∀ θ, ρ (w θ) = pathToCircle (α.trans ω) θ := by
  have hw : ∀ θ, pathToCircle (α.trans ω) θ ∈ Set.range ρ := fun θ =>
    hrange ⟨e θ, (G.boundary_apply (e θ)).trans (hparam θ)⟩
  exact ⟨liftFreeLoop hρ (pathToCircle (α.trans ω)) hw,
    ⟨ofManifoldRealization (w := pathToCircle (α.trans ω)) hρ e hparam hw⟩,
    fun θ => liftFreeLoop_apply hρ (pathToCircle (α.trans ω)) hw θ⟩

end Manifold

end BoundaryWordWitness

/-! ### Non-vacuity at a proper ambient loop space -/

section NonVacuity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- **The producer is reached at an ambient loop space which is not `M`.**  Take the ambient
loop space to be the image of the cell, a genuine subspace of `M`, and `ρ` the inclusion, which
is an embedding.  The boundary loop of the cell has all its values in that image, because the
frontier of the domain is contained in the domain, so
`BoundaryWordWitness.ofManifoldRealization` applies and produces a witness whose word reads
back as the boundary loop.  No hypothesis on the cell is needed.

This is the non-vacuity of the producer at a *proper* ambient loop space: see
`range_subtypeVal_image_ne_univ` for the sense in which the inclusion is not the identity. -/
theorem exists_boundaryWordWitness_image_subtypeVal (G : SingularTwoCell M)
    (param : loopCircle ≃ₜ frontier G.domain) :
    ∃ w : freeLoop ↥(⇑G '' G.domain),
      Nonempty (BoundaryWordWitness G (Subtype.val : ↥(⇑G '' G.domain) → M) w) ∧
        ∀ θ, (w θ : M) = G (param θ) := by
  have hρ : IsEmbedding (Subtype.val : ↥(⇑G '' G.domain) → M) :=
    _root_.Topology.IsEmbedding.subtypeVal
  have hw : ∀ θ, boundaryFreeLoop G param θ ∈
      Set.range (Subtype.val : ↥(⇑G '' G.domain) → M) := fun θ =>
    ⟨⟨G (param θ), (param θ : EuclideanSpace ℝ (Fin 2)),
      G.frontier_subset_domain (param θ).2, rfl⟩, rfl⟩
  exact ⟨BoundaryWordWitness.liftFreeLoop hρ (boundaryFreeLoop G param) hw,
    ⟨BoundaryWordWitness.ofManifoldRealization (w := boundaryFreeLoop G param) hρ param
      (fun _ => rfl) hw⟩,
    fun θ => BoundaryWordWitness.liftFreeLoop_apply hρ (boundaryFreeLoop G param) hw θ⟩

/-- **The ambient loop space of `exists_boundaryWordWitness_image_subtypeVal` is not the
model.**  As soon as the cell does not cover `M`, the inclusion of its image has a proper
range, so that instantiation is not the degenerate one with `X := M` and `ρ := id`.  Whether
the image of a singular two cell can be all of `M` is not decided here; the hypothesis is
stated instead. -/
theorem range_subtypeVal_image_ne_univ (G : SingularTwoCell M)
    (h : ⇑G '' G.domain ≠ Set.univ) :
    Set.range (Subtype.val : ↥(⇑G '' G.domain) → M) ≠ Set.univ := by
  rwa [Subtype.range_val]

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
