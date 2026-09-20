/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedCellInDouble

/-!
# The normality fields already available for a projected embedded disk

Moise's Lemma 2 starts from an embedded disk upstairs and projects it through the double
cover.  `DoubleCoverDiagram.exists_projected_singular_two_cell_in_double` produces that
projected cell inside the double of the downstairs manifold.  Four of the six conditions a
normal singular cell has to satisfy are already consequences of that producer, and only the
triangulation of the singular set as a one manifold and the crossing condition at the double
points need general position.

This file records those four, written in exactly the shape the normality data asks for, for
the boundary data

* `Bd`, the second copy of the boundary of the downstairs manifold inside the double, and
* `B`, the boundary neighborhood of the downstairs normal system inside the double,

so that a later general position theorem only has to supply the remaining two.  Nothing here
is new geometry: the whole content is the rewriting of the producer's conclusion, together
with the observation that the projected boundary curve lands in the boundary neighborhood.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
/-- **The four normality conditions a projected embedded disk satisfies outright.**  For a
double cover diagram and an embedded disk upstairs, the projected singular two cell in the
double of the downstairs manifold is locally injective, is at most two to one, has its
boundary curve inside the boundary neighborhood, and meets the boundary of the downstairs
manifold exactly along that boundary curve.  Its boundary curve still avoids the normal
subgroup.

The four conditions are stated literally as the corresponding conditions of a normal
singular cell over the boundary data `Bd` and `B`, so that adding a triangulation of the
singular set and the crossing condition completes the normality data. -/
theorem DoubleCoverDiagram.exists_projected_cell_normal_fields
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    let B := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)),
      G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
      (∀ x ∈ G.domain, ∃ U ∈ 𝓝[G.domain] x, InjOn G U) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
      Set.range G.boundary ⊆ B ∧
      G '' G.domain ∩ Bd = Set.range G.boundary ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q)
        S.normalSubgroup := by
  classical
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι : E → E × E × ℝ :=
    simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  dsimp only
  have hmain := R.exists_projected_singular_two_cell_in_double D
  dsimp only at hmain
  obtain ⟨G, γ, q, hdom, hγ, -, -, hfront, -, hinter, hboundaryG, havoid, -, hlocal,
    hcardG, -⟩ := hmain
  have hnbhd : Set.range (fun θ => ((γ θ : E))) ⊆ S.boundaryNeighborhood.space := by
    rintro _ ⟨θ, rfl⟩
    exact (γ θ).2
  refine ⟨G, γ, q, hdom, hγ, Covering.isLocallyInjective_domRestrict_iff.mp hlocal, hcardG,
    ?_, ?_, havoid⟩
  · rintro _ ⟨x, rfl⟩
    have hmem : ((G.boundary x : (double 3 K).space) : E × E × ℝ) ∈
        ι '' Set.range (fun θ => (γ θ : E)) := by
      rw [← hboundaryG]
      exact ⟨x, rfl⟩
    exact image_mono hnbhd hmem
  · rw [← hfront]
    exact hinter

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
