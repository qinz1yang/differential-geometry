/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ComplexityInduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskOfDoubleCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoEndpoint
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryLoop

/-!
# The spine of Moise's Lemma 2

`LemmaTwoStatement` is an undecomposed open root: a double cover reduction and an embedded disk
upstairs have to produce an embedded disk downstairs.  Three legs of the argument are already
proved, and this file is the assembly that joins them, leaving exactly two obligations.

* The **entry** leg `DoubleCoverDiagram.exists_projected_singular_two_cell_with_boundaryLoop_lift`
  projects the upstairs disk into the double of the downstairs manifold complex.  The projected
  cell is locally injective, at most two to one, lies on the `|K|` side, is proper over the seam,
  and its boundary circle is parametrised by a free loop of the boundary neighborhood avoiding the
  normal subgroup.
* The **induction** leg, `exists_complexity_eq_zero_of_descendingSurgery_of_motive` in
  `NormalSingularCellData`, iterates a descending surgery down to complexity zero while carrying
  an arbitrary invariant.
* The **return** leg `NormalSystem.exists_embeddedDisk_of_nonsingular_two_cell_in_double` reads a
  nonsingular cell of the double back as a proper piecewise linear embedded disk downstairs.

What is missing between them is Moise's opening sentence (general position, p. 184) and his Cases
1--4 (the surgery itself, pp. 184--187).  They appear here as `GeneralPositionInDoubleStatement`
and `DescentStepStatement`, and `lemmaTwoStatement_of_generalPosition_of_descentStep` derives the
whole of `LemmaTwoStatement` from the two of them.  Neither obligation mentions an embedded disk
of the base system or the double cover, and neither mentions the other.

## The invariant carried through the induction

The induction transports, from the cell general position produces to the nonsingular cell the
return leg consumes, three clauses: the cell stays on the `|K|` side of the double, its boundary
circle has the boundary neighborhood as a *relative neighborhood* in the seam, and that circle is
parametrised by a free loop avoiding the normal subgroup.  The first and the third are exactly
what the return leg asks for; the second is the buffer clause the tube producer of Moise's Cases
1--4 needs, in the spelling the tree already uses for it
(`DoubleCoverDiagram.exists_boundaryNeighborhood_radius`).

## Where the buffer clause sits, and why

The buffer is **not** available at the entry.  A `DoubleCoverDiagram` relates the two boundary
neighborhoods only through its field `boundaryMap`, which places the projected boundary circle
inside the downstairs boundary neighborhood and says nothing more; the neighborhood strengthening
is an extra hypothesis, supplied by the cover producers of `LoopTheorem.CoverReduction` and
dropped by `DoubleCoverReduction`.  So the buffer is asked of general position, as part of its
conclusion, and not of the cell it starts from: `GeneralPositionInDoubleStatement` assumes only
that the given boundary circle lies in the boundary neighborhood, and has to return a normal cell
whose boundary circle lies in its relative interior.  Putting the buffer in the hypothesis instead
would make the obligation unusable at the entry of Lemma 2, and leaving it out entirely would
break the induction step, whose tube producer consumes it.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
/-- **The general position obligation of Moise's Lemma 2 (p. 184, first paragraph).**  Let `S` be
a normal system, `Bd` the copy of the boundary of its manifold complex inside the double, `B` the
copy of its boundary neighborhood, and `C` the copy of the manifold complex itself.  Given a
singular two cell `G` of the double which is locally injective, at most two to one, has its
boundary circle in `B` and meets `Bd` exactly along that circle, stays in `C`, is proper over
`Bd`, and whose boundary circle is parametrised by a free loop `γ` of the boundary neighborhood
avoiding the normal subgroup, there is a *normal* singular two cell `A` on the same source disk
which still stays in `C`, whose boundary circle has `B` as a relative neighborhood in `Bd`, and
which is again parametrised by a free loop avoiding the normal subgroup.

This is Moise's "we can make slight perturbations of `D`, preserving the stated properties of `D`,
so as to put `|D|` into general position", for which he gives no proof.  It is an obligation, not
a theorem: nothing in this file proves it, and it mentions neither the double cover nor an
embedded disk.  The relative neighborhood clause is a strengthening of the plain inclusion
`Set.range A.boundary ⊆ B` assumed of `G`; general position has to produce it, because the entry
cell of Lemma 2 does not have it and the surgery step needs it. -/
def GeneralPositionInDoubleStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E),
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    let B := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∀ (G : SingularTwoCell (double 3 K).space)
      (β : ContinuousMap loopCircle (frontier G.domain))
      (γ : freeLoop S.boundaryNeighborhoodSpace),
      (∀ x ∈ G.domain, ∃ U ∈ 𝓝[G.domain] x, Set.InjOn G U) →
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) →
      Set.range G.boundary ⊆ B →
      G '' G.domain ∩ Bd = Set.range G.boundary →
      MapsTo G G.domain C →
      G.domain ∩ G ⁻¹' Bd = frontier G.domain →
      Function.Surjective β →
      (∀ θ, ((G (β θ) : (double 3 K).space) : E × E × ℝ) = ι (γ θ)) →
      ¬loopClassMeets γ S.basepoint S.normalSubgroup →
      ∃ (A : SingularTwoCell (double 3 K).space) (_ : NormalSingularCellData A Bd B),
        A.domain = G.domain ∧ MapsTo A A.domain C ∧
        (∀ z ∈ Set.range A.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier A.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((A (c θ) : (double 3 K).space) : E × E × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup

open Classical in
/-- **The descent step obligation of Moise's Lemma 2 (Cases 1--4, pp. 184--187).**  A normal
singular two cell of the double whose singular set is not already empty, which stays on the `|K|`
side, whose boundary circle has the boundary neighborhood as a relative neighborhood in the seam,
and whose boundary circle avoids the normal subgroup, admits a descending surgery -- a normal cell
over the same boundary data with strictly smaller singular set complexity -- with all three
clauses again.

The complexity belongs to the chosen normality datum, not to the underlying cell, so the
obligation quantifies over pairs of a cell and a datum for it, and the surgery is compared only
with the datum it was built from.  This is an obligation, not a theorem: nothing in this file
proves it, and it mentions neither the double cover nor an embedded disk. -/
def DescentStepStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E),
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    let B := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∀ (D₀ : SingularTwoCell (double 3 K).space) (hD₀ : NormalSingularCellData D₀ Bd B),
      hD₀.singularSet.complexity ≠ 0 →
      MapsTo D₀ D₀.domain C →
      (∀ z ∈ Set.range D₀.boundary, B ∈ 𝓝[Bd] z) →
      (∃ (c : loopCircle ≃ₜ frontier D₀.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
        (∀ θ, ((D₀ (c θ) : (double 3 K).space) : E × E × ℝ) = ι (δ θ)) ∧
          ¬loopClassMeets δ S.basepoint S.normalSubgroup) →
      ∃ Sg : hD₀.DescendingSurgery,
        MapsTo Sg.cell Sg.cell.domain C ∧
        (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier Sg.cell.domain)
          (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((Sg.cell (c θ) : (double 3 K).space) : E × E × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup

/-- **The spine of Moise's Lemma 2.**  General position in the double and the descent step of
Cases 1--4 together give the whole of `LemmaTwoStatement`.

The proof is the assembly and nothing else.  The projected cell of the upstairs embedded disk
supplies the hypotheses of general position; general position supplies a normal cell together with
the invariant; the complexity induction carries the invariant down to a cell of complexity zero,
which is injective on its source disk; and the conversion of a nonsingular cell of the double into
an embedded disk of the base system finishes.  The two side conditions `LemmaTwoStatement` imposes
on the covering system are not used here: they are part of a fixed statement and are consumed
elsewhere in the tower. -/
theorem lemmaTwoStatement_of_generalPosition_of_descentStep
    (generalPosition : GeneralPositionInDoubleStatement)
    (descentStep : DescentStepStatement) :
    LemmaTwoStatement := by
  classical
  intro F _ _ _ M S T R _ _ hdisk
  obtain ⟨D⟩ := hdisk
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
    (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
  let B := ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
    (ι '' S.boundaryNeighborhood.space)
  obtain ⟨G, γ, q, β, -, -, -, hmapC, hproperC, hloc, hcard, havoid, hβsurj, hβ⟩ :=
    R.toDoubleCoverDiagram.exists_projected_singular_two_cell_with_boundaryLoop_lift D
  have hfrontC : frontier C = Bd := by
    have hC : C = ((↑) : (double 3 K).space → F × F × ℝ) ⁻¹'
        (glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id).space := by
      rw [glued₂_space]
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K S.isManifold
  have havoidγ : ¬loopClassMeets γ S.basepoint S.normalSubgroup := by
    have h := havoid
    rw [normalSystemLoopConjugacyClass_eq_conjugacyClass γ q] at h
    exact h
  have hBsub : Set.range G.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨θ, rfl⟩ := hβsurj x
    exact ⟨(γ θ : F), (γ θ).2, (hβ θ).symm⟩
  have hproperBd : G.domain ∩ G ⁻¹' Bd = frontier G.domain := by
    rw [← hfrontC]
    exact hproperC
  have hinterBd : G '' G.domain ∩ Bd = Set.range G.boundary := by
    rw [← image_inter_preimage, hproperBd]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  obtain ⟨A, hA, -, hAside, hAbuffer, hAloop⟩ :=
    generalPosition S G β γ (Covering.isLocallyInjective_domRestrict_iff.mp hloc) hcard
      hBsub hinterBd hmapC hproperBd hβsurj hβ havoidγ
  obtain ⟨A', hA', -, hnonsingular, -, hside, -, hloop⟩ :=
    NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive
      (fun A₀ _ => MapsTo A₀ A₀.domain C ∧
        (∀ z ∈ Set.range A₀.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier A₀.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((A₀ (c θ) : (double 3 K).space) : F × F × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup)
      (fun A₀ hA₀ hcomplexity hmotive =>
        descentStep S A₀ hA₀ hcomplexity hmotive.1 hmotive.2.1 hmotive.2.2)
      hA ⟨hAside, hAbuffer, hAloop⟩
  refine S.exists_embeddedDisk_of_nonsingular_two_cell_in_double A' hnonsingular ?_
    hA'.image_inter_boundary hloop
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact hside hx

end DifferentialGeometry.Topology.PiecewiseLinear
