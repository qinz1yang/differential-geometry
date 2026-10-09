/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedCellInDouble

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
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
