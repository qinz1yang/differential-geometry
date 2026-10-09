/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ComplexityInduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskOfDoubleCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoEndpoint
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryLoop

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
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
