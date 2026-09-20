/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundarySurgeryCellPredicate
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitnessOfCell

/-!
# The two boundary case candidates of one boundary branch cut

`LoopTheorem.BoundaryWordWitnessOfCell` produces a boundary word witness from a *two arc match*:
the recorded two arc parametrisation of the boundary circle of a candidate cell, matched against
two injective paths of the ambient loop space sweeping out the same two sets.  What it could not
do is supply the match, because the three producers of `LoopTheorem.CutAndPaste` and
`BoundaryWordFourArcs` each chose their own three piece cut.  They now take the cut as an input,
so one cut feeds all three, and the arcs of the candidates and the arcs of the four arc word of
`D` are arcs of the same decomposition.  This file draws the consequence.

## The orientation of a recorded two arc word

A candidate records its boundary circle as `∀ θ, G (e θ) = pathToCircle (α.trans ω) θ` with
`α` sweeping out the image of one arc of the cut and `ω` the image of the other, and the cores
now record which of the two marked points of the cut each endpoint of `α` is.  Both orders
occur: nothing in the gluing pins the direction in which the parametrisation runs, and the
recorded endpoint dichotomy is exactly that ambiguity.
`BoundaryWordWitness.exists_of_twoArcMatch_of_endpoints` absorbs it.  In the aligned case it is
`BoundaryWordWitness.exists_of_twoArcMatch`; in the reversed case the two arcs match the two
*reversed* paths, which gives a witness over the reversed word, and
`BoundaryWordWitness.ofReversedWord` reads the witness backwards — the boundary parametrisation
is precomposed with negation on the loop circle, which is again a homeomorphism, and the free
homotopy is composed with it.  Reversing twice is the identity, and
`DifferentialGeometry.Topology.pathToCircle_symm` together with
`DifferentialGeometry.Topology.pathToCircle_trans_homotopic_comm` identifies the word one lands
on with the word one wants.  So the two arc match never needs the orientation to be known.

## The combined producer

`NormalSingularCellData.exists_boundaryCandidates_of_cut` runs the three producers on one cut.
It returns the four arc word of `D` — with the first and the third arc the traces of `D₁` and
`D₃`, and with all four arcs injective — the direct candidate `Gd`, the cross candidate `G`,
each with its recorded two arc word, the images of those arcs *described through the same four
arcs*, and the endpoint dichotomy of each.  It also returns
`NormalSingularCellData.IsBoundarySurgeryCell` and `NormalSingularCellData.IsCrossRegluedCell`
for the two candidates, so the assemblies of `LoopTheorem.BoundarySurgeryCellPredicate` apply to
exactly these two cells.  Those two predicates quantify the cut existentially, so this direction
is the easy one; what is new is that the two cells now come out of *one* cut together with the
word they have to be compared with.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace BoundaryWordWitness

section Reverse

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

/-- **A witness read backwards.**  Precomposing the boundary parametrisation of a witness with
negation on the loop circle is again a boundary parametrisation, because negation is a
homeomorphism of the loop circle; the realisation is the old one at the negated parameter, and
the free homotopy is the old one composed with negation.  The word of the new witness is the old
word read backwards. -/
def ofReversedWord {w : freeLoop X} (W : BoundaryWordWitness G ρ w) :
    BoundaryWordWitness G ρ (w.comp ⟨fun θ => -θ, continuous_neg⟩) where
  param := (Homeomorph.neg loopCircle).trans W.param
  loop := W.loop.comp ⟨fun θ => -θ, continuous_neg⟩
  realizes := fun θ => W.realizes (-θ)
  homotopic := W.homotopic.comp (ContinuousMap.Homotopic.refl _)

/-- Reading a word backwards twice returns the word. -/
theorem comp_neg_comp_neg (w : freeLoop X) :
    (w.comp ⟨fun θ => -θ, continuous_neg⟩).comp
        (⟨fun θ => -θ, continuous_neg⟩ : C(loopCircle, loopCircle)) = w :=
  ContinuousMap.ext fun θ => by
    change w (- -θ) = w θ
    rw [neg_neg]

/-- **The two arc match, in either orientation.**  The hypotheses of
`BoundaryWordWitness.exists_of_twoArcMatch` ask the recorded arc `α` to run from the image of
`a` to the image of `b`; a gluing records its boundary circle without pinning that direction,
and delivers instead the dichotomy `hend`.  In the aligned case this is the match itself.  In
the reversed case the recorded arcs match the reversed paths, so the match gives a witness over
the reversed word; reading that witness backwards and rotating the resulting concatenation
returns a witness over the word asked for. -/
theorem exists_of_twoArcMatch_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q) {x y : M}
    {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P) (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (P.trans Q))) := by
  rcases hend with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst hx
    subst hy
    exact exists_of_twoArcMatch hρ e hP hQ hparam hα hω
  · subst hx
    subst hy
    have hPsymm : Function.Injective ⇑P.symm := by
      intro s t hst
      have h : P (unitInterval.symm s) = P (unitInterval.symm t) := hst
      exact unitInterval.symm_bijective.injective (hP h)
    have hQsymm : Function.Injective ⇑Q.symm := by
      intro s t hst
      have h : Q (unitInterval.symm s) = Q (unitInterval.symm t) := hst
      exact unitInterval.symm_bijective.injective (hQ h)
    obtain ⟨W⟩ := exists_of_twoArcMatch hρ e hPsymm hQsymm hparam
      (by rwa [Path.symm_range]) (by rwa [Path.symm_range])
    have hword : pathToCircle (P.symm.trans Q.symm) =
        (pathToCircle (Q.trans P)).comp ⟨fun θ => -θ, continuous_neg⟩ := by
      rw [← Path.trans_symm Q P, pathToCircle_symm]
    rw [hword] at W
    have hback := W.ofReversedWord
    rw [comp_neg_comp_neg] at hback
    exact ⟨hback.ofHomotopicWord (pathToCircle_trans_homotopic_comm Q P)⟩

/-- **The endpoint reversing direct candidate word, in either orientation.**  The two arc match
with the second arc read backwards, and with the orientation of the recorded parametrisation
left open. -/
theorem exists_of_twoArcMatch_reversing_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b}
    (hσ : Function.Injective ⇑σ) (hυ : Function.Injective ⇑υ) {x y : M}
    {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑σ) (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans υ.symm))) := by
  refine exists_of_twoArcMatch_of_endpoints hρ e hσ ?_ hparam hα ?_ hend
  · intro s t hst
    have h : υ (unitInterval.symm s) = υ (unitInterval.symm t) := hst
    exact unitInterval.symm_bijective.injective (hυ h)
  · rwa [Path.symm_range]

/-- **The endpoint reversing cross candidate word, in either orientation.**  The four arc word
of the cross candidate, read off its two arc boundary through the cyclic rotation of
`BoundaryWordWitness.exists_of_fourArcMatch_reversing`, with the orientation of the recorded
parametrisation left open.  The first recorded arc carries the three letter concatenation
`τ.trans (σ.trans φ)`, so the aligned case is the one in which the parametrisation starts at the
image of `b`. -/
theorem exists_of_fourArcMatch_reversing_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b} {τ φ : Path b a}
    (hlong : Function.Injective ⇑(τ.trans (σ.trans φ))) (hυ : Function.Injective ⇑υ)
    {x y : M} {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑(τ.trans (σ.trans φ)))
    (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ)
    (hend : (x = ρ b ∧ y = ρ a) ∨ (x = ρ a ∧ y = ρ b)) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ))))) := by
  obtain ⟨W⟩ := exists_of_twoArcMatch_of_endpoints hρ e hlong hυ hparam hα hω hend
  have h₁ := pathToCircle_homotopic (Path.Homotopic.trans_assoc τ (σ.trans φ) υ)
  have h₂ := pathToCircle_trans_homotopic_comm τ ((σ.trans φ).trans υ)
  have h₃ := pathToCircle_homotopic (Path.Homotopic.trans_assoc (σ.trans φ) υ τ)
  have h₄ := pathToCircle_homotopic (Path.Homotopic.trans_assoc σ φ (υ.trans τ))
  exact ⟨W.ofHomotopicWord (((h₁.trans h₂).trans h₃).trans h₄)⟩

/-- **The endpoint preserving cross candidate word, in either orientation.**  The endpoint
preserving twin of `BoundaryWordWitness.exists_of_fourArcMatch_reversing_of_endpoints`: the
second and the fourth letter are loops and are traversed backwards, and the first recorded arc
carries `φ.symm.trans (σ.trans τ.symm)`, which starts at the image of `a`. -/
theorem exists_of_fourArcMatch_preserving_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ : Path a b} {τ : Path b b}
    {υ : Path b a} {φ : Path a a}
    (hlong : Function.Injective ⇑(φ.symm.trans (σ.trans τ.symm)))
    (hυ : Function.Injective ⇑υ) {x y : M} {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑(φ.symm.trans (σ.trans τ.symm)))
    (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    Nonempty (BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) := by
  obtain ⟨W⟩ := exists_of_twoArcMatch_of_endpoints hρ e hlong hυ hparam hα hω hend
  have h₁ := pathToCircle_homotopic (Path.Homotopic.trans_assoc φ.symm (σ.trans τ.symm) υ)
  have h₂ := pathToCircle_trans_homotopic_comm φ.symm ((σ.trans τ.symm).trans υ)
  have h₃ := pathToCircle_homotopic (Path.Homotopic.trans_assoc (σ.trans τ.symm) υ φ.symm)
  have h₄ := pathToCircle_homotopic (Path.Homotopic.trans_assoc σ τ.symm (υ.trans φ.symm))
  exact ⟨W.ofHomotopicWord (((h₁.trans h₂).trans h₃).trans h₄)⟩

/-- **Both boundary word witnesses of an endpoint reversing boundary branch cut.**  The two
candidates are compared with the same four arc word: the four sets `J₁`, `J₂`, `J₃`, `J₄` are
the images in `M` of the four arcs of the boundary circle that was cut, the four letters of the
word sweep them out through `ρ`, the direct candidate records the first and the third of them as
its two arcs, and the cross candidate records the union of the second, the first and the fourth,
and again the third.  Nothing about the two cells is used beyond those recorded arcs and the
recorded endpoints, and the orientation of either recorded parametrisation is left open. -/
theorem exists_pair_of_fourArcMatch_reversing [T2Space M] {Gd Gc : SingularTwoCell M}
    {J₁ J₂ J₃ J₄ : Set M} (hρ : IsEmbedding ρ) {a b : X} {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ρ '' Set.range ⇑σ = J₁) (hτ : ρ '' Set.range ⇑τ = J₂)
    (hυ : ρ '' Set.range ⇑υ = J₃) (hφ : ρ '' Set.range ⇑φ = J₄)
    (hσinj : Function.Injective ⇑σ) (hυinj : Function.Injective ⇑υ)
    (hlong : Function.Injective ⇑(τ.trans (σ.trans φ)))
    {xd yd : M} {αd : Path xd yd} {ωd : Path yd xd}
    (ed : loopCircle ≃ₜ frontier Gd.domain)
    (hαd : Set.range ⇑αd = J₁) (hωd : Set.range ⇑ωd = J₃)
    (hparamd : ∀ θ, Gd (ed θ) = pathToCircle (αd.trans ωd) θ)
    (hendd : (xd = ρ a ∧ yd = ρ b) ∨ (xd = ρ b ∧ yd = ρ a))
    {xc yc : M} {αc : Path xc yc} {ωc : Path yc xc}
    (ec : loopCircle ≃ₜ frontier Gc.domain)
    (hαc : Set.range ⇑αc = J₂ ∪ (J₁ ∪ J₄)) (hωc : Set.range ⇑ωc = J₃)
    (hparamc : ∀ θ, Gc (ec θ) = pathToCircle (αc.trans ωc) θ)
    (hendc : (xc = ρ b ∧ yc = ρ a) ∨ (xc = ρ a ∧ yc = ρ b)) :
    Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm))) ∧
      Nonempty (BoundaryWordWitness Gc ρ
        (pathToCircle (σ.trans (φ.trans (υ.trans τ))))) := by
  constructor
  · exact exists_of_twoArcMatch_reversing_of_endpoints hρ ed hσinj hυinj hparamd
      (hαd.trans hσ.symm) (hωd.trans hυ.symm) hendd
  · refine exists_of_fourArcMatch_reversing_of_endpoints hρ ec hlong hυinj hparamc ?_
      (hωc.trans hυ.symm) hendc
    refine hαc.trans ?_
    rw [Path.trans_range, Path.trans_range, Set.image_union, Set.image_union, hσ, hτ, hφ]

/-- **Both boundary word witnesses of an endpoint preserving boundary branch cut.**  The
endpoint preserving twin of `BoundaryWordWitness.exists_pair_of_fourArcMatch_reversing`: the
second and the fourth letter are loops, the direct candidate word is `σ.trans υ` and the cross
candidate word is `σ.trans (τ.symm.trans (υ.trans φ.symm))`.  The recorded arcs of the two
candidates are described by the same four sets and in the same way; only the letters of the word
change type. -/
theorem exists_pair_of_fourArcMatch_preserving [T2Space M] {Gd Gc : SingularTwoCell M}
    {J₁ J₂ J₃ J₄ : Set M} (hρ : IsEmbedding ρ) {a b : X} {σ : Path a b} {τ : Path b b}
    {υ : Path b a} {φ : Path a a}
    (hσ : ρ '' Set.range ⇑σ = J₁) (hτ : ρ '' Set.range ⇑τ = J₂)
    (hυ : ρ '' Set.range ⇑υ = J₃) (hφ : ρ '' Set.range ⇑φ = J₄)
    (hσinj : Function.Injective ⇑σ) (hυinj : Function.Injective ⇑υ)
    (hlong : Function.Injective ⇑(φ.symm.trans (σ.trans τ.symm)))
    {xd yd : M} {αd : Path xd yd} {ωd : Path yd xd}
    (ed : loopCircle ≃ₜ frontier Gd.domain)
    (hαd : Set.range ⇑αd = J₁) (hωd : Set.range ⇑ωd = J₃)
    (hparamd : ∀ θ, Gd (ed θ) = pathToCircle (αd.trans ωd) θ)
    (hendd : (xd = ρ a ∧ yd = ρ b) ∨ (xd = ρ b ∧ yd = ρ a))
    {xc yc : M} {αc : Path xc yc} {ωc : Path yc xc}
    (ec : loopCircle ≃ₜ frontier Gc.domain)
    (hαc : Set.range ⇑αc = J₂ ∪ (J₁ ∪ J₄)) (hωc : Set.range ⇑ωc = J₃)
    (hparamc : ∀ θ, Gc (ec θ) = pathToCircle (αc.trans ωc) θ)
    (hendc : (xc = ρ a ∧ yc = ρ b) ∨ (xc = ρ b ∧ yc = ρ a)) :
    Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ))) ∧
      Nonempty (BoundaryWordWitness Gc ρ
        (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) := by
  constructor
  · exact exists_of_twoArcMatch_of_endpoints hρ ed hσinj hυinj hparamd
      (hαd.trans hσ.symm) (hωd.trans hυ.symm) hendd
  · refine exists_of_fourArcMatch_preserving_of_endpoints hρ ec hlong hυinj hparamc ?_
      (hωc.trans hυ.symm) hendc
    refine hαc.trans ?_
    rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range,
      Set.image_union, Set.image_union, hσ, hτ, hφ]
    ext z
    simp only [Set.mem_union]
    tauto

end Reverse

end BoundaryWordWitness

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

/-- **Both boundary case candidates of one cut, together with the four arc word they are
compared with.**  The three producers are run on the *same* three piece cut, so the two arcs of
the direct candidate are the traces of `D₁` and `D₃` on the boundary circle of `D`, which are
the first and the third arc of the four arc word, and the two arcs of the cross candidate are
the union of the second, the first and the fourth arc, and again the third arc.  Each candidate
also carries the two marked points of the cut as the endpoints of its recorded parametrisation,
in one of the two orders.  This is exactly the data that
`BoundaryWordWitness.exists_of_twoArcMatch_of_endpoints` and its four arc companions consume.
The two candidates satisfy the two naming predicates, so the boundary case assemblies apply to
them. -/
theorem exists_boundaryCandidates_of_cut [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A C p q r s g D₁ D₂ D₃) :
    ∃ (A₂ A₄ : Set (EuclideanSpace ℝ (Fin 2))) (u v : EuclideanSpace ℝ (Fin 2))
        (p' q' u' v' : frontier D.domain) (σ₀ : Path p' q') (τ₀ : Path q' u')
        (υ₀ : Path u' v') (φ₀ : Path v' p') (ev : loopCircle ≃ₜ frontier D.domain)
        (Gd G : SingularTwoCell M) (xd yd : M) (αd : Path xd yd) (ωd : Path yd xd)
        (ed : loopCircle ≃ₜ frontier Gd.domain) (xc yc : M) (αc : Path xc yc)
        (ωc : Path yc xc) (ec : loopCircle ≃ₜ frontier G.domain),
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c G ∧
      (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (u' : EuclideanSpace ℝ (Fin 2)) = u ∧ (v' : EuclideanSpace ℝ (Fin 2)) = v ∧
      Set.range (fun t => ((σ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₁.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((τ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₃.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((φ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      frontier D.domain = (D₁.domain ∩ frontier D.domain) ∪
        (A₂ ∪ ((D₃.domain ∩ frontier D.domain) ∪ A₄)) ∧
      (∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      Function.Injective ⇑σ₀ ∧ Function.Injective ⇑τ₀ ∧
      Function.Injective ⇑υ₀ ∧ Function.Injective ⇑φ₀ ∧
      ((D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p)) ∧
      Set.range ⇑αd = ⇑D '' (D₁.domain ∩ frontier D.domain) ∧
      Set.range ⇑ωd = ⇑D '' (D₃.domain ∩ frontier D.domain) ∧
      (∀ θ, Gd (ed θ) = pathToCircle (αd.trans ωd) θ) ∧
      ((xd = D p ∧ yd = D q) ∨ (xd = D q ∧ yd = D p)) ∧
      Set.range ⇑αc = ⇑D '' (A₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ A₄)) ∧
      Set.range ⇑ωc = ⇑D '' (D₃.domain ∩ frontier D.domain) ∧
      (∀ θ, G (ec θ) = pathToCircle (αc.trans ωc) θ) ∧
      ((xc = D p ∧ yc = D q) ∨ (xc = D q ∧ yc = D p)) := by
  obtain ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev,
    ⟨-, -, -, -, -, -, hp', hq', hu', hv', hr₁, hr₂, hr₃, hr₄, hJ, hev, hpair⟩,
    hσinj, hτinj, hυinj, hφinj, -, -, -, -, hkey⟩ :=
    hD.exists_boundary_four_arc_word_of_cut hcut
  obtain ⟨Gd, pullback, ⟨hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
    hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
    himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
    htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
    R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj, hρ₀range, hκ₀range,
    he₀, hclosed₁, hclosed₂, hclosed₃, hdomains, hinter₁₂, hinter₂₃, hkept, hband⟩,
    xd, yd, αd, ωd, ed, hαd, hωd, hparamd, hendd⟩ :=
    hD.exists_boundary_surgery_cell_of_cut hcut
  obtain ⟨P, Q, P', Q', A', R, T, a, b, f₁, f₂, h, f₃, H, G, hcbody,
    xc, yc, αc, ωc, ec, hαc, hωc, hparamc, hendc⟩ :=
    hD.exists_cross_reglued_cell_of_cut hcut
  refine ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev, Gd, G,
    xd, yd, αd, ωd, ed, xc, yc, αc, ωc, ec, ?_, ?_, hp', hq', hu', hv',
    hr₁, hr₂, hr₃, hr₄, hJ, hev, hσinj, hτinj, hυinj, hφinj, hpair,
    hαd, hωd, hparamd, hendd, ?_, hωc, hparamc, hendc⟩
  · exact ⟨A, C, D₁.domain ∩ frontier D.domain, D₃.domain ∩ frontier D.domain,
      p, q, r, s, g, pullback, hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
      hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
      himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
      htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
      R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj, hρ₀range, hκ₀range,
      he₀, D₁.domain, D₂.domain, D₃.domain, hclosed₁, hclosed₂, hclosed₃, hdomains,
      hinter₁₂, hinter₂₃, hkept, hband⟩
  · exact ⟨A, C, D₁.domain, D₂.domain, D₃.domain, P, Q, P', Q', A', R, T,
      p, q, r, s, a, b, g, f₁, f₂, h, f₃, H, hcbody⟩
  · rw [hαc, hkey]

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
