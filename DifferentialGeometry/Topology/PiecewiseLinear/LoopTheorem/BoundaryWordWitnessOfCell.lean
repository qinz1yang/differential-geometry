/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.InjectivePathReparam
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness

/-!
# Boundary word witnesses from a two arc parametrisation of a candidate cell

The boundary case assemblies of `LoopTheorem.CrossRegluedCellPredicate` and
`LoopTheorem.BoundarySurgeryCellPredicate` still take the two boundary word witnesses
`Wdirect` and `Wraw` as hypotheses.  Both candidate producers of `LoopTheorem.CutAndPaste`
now record the boundary circle of their cell as a *two arc* loop of `M`, together with
injective source parametrisations of the two arcs.  This file supplies the two arc passage.

## The brick

`BoundaryWordWitness.exists_of_twoArcMatch` takes the recorded two arc parametrisation
`∀ θ, G (e θ) = pathToCircle (α.trans ω) θ` of a cell `G` and two paths `P`, `Q` of `X` whose
concatenation is the desired word, and produces a witness as soon as

* `P` and `Q` are injective, and
* `Set.range α = ρ '' Set.range P` and `Set.range ω = ρ '' Set.range Q`.

Nothing else is needed.  In particular the hypothesis `B ⊆ Set.range ρ` of the assemblies is
*not* used: the two range equalities already place the boundary curve inside the range of
`ρ`, so the arcs lift to `X` by `BoundaryWordWitness.liftPath`, and there they are compared
with `P` and `Q` by `Path.Homotopic.of_injective_of_range_eq`.  The homotopy produced by that
lemma is a reparametrisation, so the comparison never leaves the arc; the free homotopy of
the witness is the image of a relative homotopy of paths under
`DifferentialGeometry.Topology.pathToCircle_homotopic`.  `T2Space X` is not assumed: it comes
from `Topology.IsEmbedding.t2Space`, the ambient loop space being embedded in a Hausdorff `M`.

## The source-side cross match

The source-side cross match is supplied by `LoopTheorem.BoundaryCaseFromSource`, where
injective arcs are compared on the source boundary and path homotopies are pushed through a
continuous realisation map.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace BoundaryWordWitness

/-! ### Lifting a path along the ambient embedding -/

section Lift

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {ρ : X → M}

/-- **The lift of a path through an embedding.**  A path of `M` running between two points of
the range of an embedding `ρ : X → M`, and having all its values there, is the image of a path
of `X` with the prescribed endpoints.  Only the inducing part of `hρ` is used for continuity
and only its injectivity for the endpoints, exactly as in
`BoundaryWordWitness.liftFreeLoop`; no section of `ρ` and no local triviality is needed. -/
noncomputable def liftPath (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) : Path a b where
  toFun t := Classical.choose (Set.mem_range.mp (hγ t))
  continuous_toFun := hρ.isInducing.continuous_iff.mpr <| by
    have hspec : (ρ ∘ fun t => Classical.choose (Set.mem_range.mp (hγ t))) = ⇑γ :=
      funext fun t => Classical.choose_spec (Set.mem_range.mp (hγ t))
    rw [hspec]
    exact γ.continuous
  source' := hρ.injective ((Classical.choose_spec (Set.mem_range.mp (hγ 0))).trans γ.source)
  target' := hρ.injective ((Classical.choose_spec (Set.mem_range.mp (hγ 1))).trans γ.target)

/-- The lifted path really is a lift: reading it back through `ρ` returns the original path of
`M`.  This is not a `simp` lemma, because its left-hand side has the variable `ρ` as head
symbol and would match every term. -/
theorem liftPath_apply (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) (t : unitInterval) : ρ (liftPath hρ γ hγ t) = γ t :=
  Classical.choose_spec (Set.mem_range.mp (hγ t))

/-- The image of the lifted path is the set the original path sweeps out, read in `X`.  An
embedding is injective, so taking images along it reflects equality of sets. -/
theorem range_liftPath (hρ : IsEmbedding ρ) {a b : X} (γ : Path (ρ a) (ρ b))
    (hγ : ∀ t, γ t ∈ Set.range ρ) {S : Set X} (hS : Set.range ⇑γ = ρ '' S) :
    Set.range ⇑(liftPath hρ γ hγ) = S := by
  refine hρ.injective.image_injective ?_
  rw [← hS, ← Set.range_comp]
  exact congrArg Set.range (funext fun t => liftPath_apply hρ γ hγ t)

end Lift

/-! ### Changing the word across a free homotopy -/

section Word

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

/-- **A witness is a witness over any freely homotopic word.**  The realisation of the
boundary is untouched; only the homotopical comparison is composed with the given free
homotopy.  This is what carries a witness across the cyclic rotation relating the recorded
boundary of a candidate to the word the selection step consumes. -/
def ofHomotopicWord {w₁ w₂ : freeLoop X} (W : BoundaryWordWitness G ρ w₁)
    (h : w₁.Homotopic w₂) : BoundaryWordWitness G ρ w₂ where
  param := W.param
  loop := W.loop
  realizes := W.realizes
  homotopic := W.homotopic.trans h

end Word

/-! ### The two arc match -/

section Match

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

/-- **A two arc boundary matching two injective paths of the ambient loop space is a
witness.**  Let the boundary circle of `G` be parametrised by the concatenation of two paths
`α`, `ω` of `M` running between the images of two points `a`, `b` of the ambient loop space,
and let `P : Path a b` and `Q : Path b a` be injective paths sweeping out the same two sets.
Then `G` carries a boundary word witness over `pathToCircle (P.trans Q)`.

The two arcs lift to `X` because the range equalities put them inside the range of `ρ`; the
lifts have the same images as `P` and `Q` because an embedding is injective; and inside an arc
two paths with the same endpoints are homotopic, which is
`Path.Homotopic.of_injective_of_range_eq`.  The endpoint preserving direct candidate word
`σ.trans υ` is this statement with `P := σ` and `Q := υ`. -/
theorem exists_of_twoArcMatch [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P) (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (P.trans Q))) := by
  have : T2Space X := hρ.t2Space
  have hαmem : ∀ t, α t ∈ Set.range ρ := by
    intro t
    have ht : α t ∈ Set.range ⇑α := Set.mem_range_self t
    rw [hα] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hωmem : ∀ t, ω t ∈ Set.range ρ := by
    intro t
    have ht : ω t ∈ Set.range ⇑ω := Set.mem_range_self t
    rw [hω] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hPhom : (liftPath hρ α hαmem).Homotopic P :=
    Path.Homotopic.of_injective_of_range_eq hP (range_liftPath hρ α hαmem hα)
  have hQhom : (liftPath hρ ω hωmem).Homotopic Q :=
    Path.Homotopic.of_injective_of_range_eq hQ (range_liftPath hρ ω hωmem hω)
  refine ⟨{ param := e
            loop := pathToCircle ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
            realizes := fun θ => ?_
            homotopic := pathToCircle_homotopic (hPhom.hcomp hQhom) }⟩
  rw [hparam θ]
  exact (pathToCircle_eq_of_forall ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
    (α.trans ω) (trans_apply_eq_map (fun t => (liftPath_apply hρ α hαmem t).symm)
      (fun t => (liftPath_apply hρ ω hωmem t).symm)) θ).symm

/-- **The endpoint reversing direct candidate word.**  The two arc match with the second arc
read backwards: the recorded arc `ω` sweeps out the image of `υ`, and the word asks for
`υ.symm`.  The reverse of an injective path is injective, and the two have the same image, so
this is `BoundaryWordWitness.exists_of_twoArcMatch` with `Q := υ.symm`. -/
theorem exists_of_twoArcMatch_reversing [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b}
    (hσ : Function.Injective ⇑σ) (hυ : Function.Injective ⇑υ)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑σ) (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans υ.symm))) := by
  refine exists_of_twoArcMatch hρ e hσ ?_ hparam hα ?_
  · intro s t hst
    have h : υ (unitInterval.symm s) = υ (unitInterval.symm t) := hst
    exact unitInterval.symm_bijective.injective (hυ h)
  · rwa [Path.symm_range]

/-! ### Non-vacuity -/

/-- **The match hypotheses are satisfiable.**  Over the ambient loop space `M` itself, with
`ρ` the identity embedding, the two range equalities hold by `Set.image_id` and the match
asks only that the two recorded arcs of the boundary be injective.  So the hypotheses of
`BoundaryWordWitness.exists_of_twoArcMatch` are not contradictory, and its conclusion is
reached at a cell whose boundary is an honest two arc circle. -/
theorem exists_of_twoArcMatch_self [T2Space M] (e : loopCircle ≃ₜ frontier G.domain)
    {y z : M} {α : Path y z} {ω : Path z y} (hα : Function.Injective ⇑α)
    (hω : Function.Injective ⇑ω) (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ) :
    Nonempty (BoundaryWordWitness G (id : M → M) (pathToCircle (α.trans ω))) :=
  exists_of_twoArcMatch (X := M) (ρ := id) _root_.Topology.IsEmbedding.id e hα hω hparam
    (Set.image_id _).symm (Set.image_id _).symm

end Match

end BoundaryWordWitness

end DifferentialGeometry.Topology.PiecewiseLinear
