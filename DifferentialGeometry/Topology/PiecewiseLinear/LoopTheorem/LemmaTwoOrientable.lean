/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
def DescentStepOrientableStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E),
    S.IsOrientableManifold →
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

theorem descentStepOrientableStatement_of_descentStepStatement
    (descentStep : DescentStepStatement) : DescentStepOrientableStatement :=
  fun S _ D₀ hD₀ hcomplexity hmapC hbuffer hloop =>
    descentStep S D₀ hD₀ hcomplexity hmapC hbuffer hloop

theorem NormalSystem.isOrientable_double_manifoldComplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) (hor : S.IsOrientableManifold) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    IsOrientable 3 (double 3 S.manifoldComplex) := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact IsOrientable.double S.manifoldComplex S.isManifold hor

def LemmaTwoBufferedOrientableStatement : Prop :=
  ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))}
    (R : NormalSystem.DoubleCoverReduction S T),
    S.IsOrientableManifold →
    T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
      frontier T.sourceComplex.space →
    T.basepoint = T.boundaryLoop 0 →
    (∀ x ∈ T.boundaryNeighborhood.space,
      S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (R.projection x)) →
    Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S)

theorem lemmaTwoBufferedOrientableStatement_of_lemmaTwoBufferedStatement
    (lemmaTwo : LemmaTwoBufferedStatement) : LemmaTwoBufferedOrientableStatement :=
  fun R _ hproper hbase hbuffer hdisk => lemmaTwo R hproper hbase hbuffer hdisk

theorem lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable
    (generalPosition : GeneralPositionInDoubleBufferedStatement)
    (descentStep : DescentStepOrientableStatement) :
    LemmaTwoBufferedOrientableStatement := by
  classical
  intro F _ _ _ M S T R hor _ _ hbuffer hdisk
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
  let π : (double 3 K).space → F := fun x => glueSnd F F (x : F × F × ℝ)
  obtain ⟨G, γ, q, β, -, hγ, -, hmapC, hproperC, hloc, hcard, havoid, hβsurj, hβ⟩ :=
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
  have hπcont : Continuous π := continuous_glueSnd.comp continuous_subtype_val
  have hπι : ∀ x ∈ K.space, glueSnd F F (ι x) = x := fun x hx =>
    glueSnd_simplicialMap K (PiecewiseLinear.boundaryComplex 3 K) id hx
  have hγK : ∀ θ, (γ θ : F) ∈ K.space := fun θ =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).property)
  have hγproj : ∀ θ, (γ θ : F) = R.projection (D.boundaryLoop θ) := by
    intro θ
    rw [hγ]
    exact R.boundaryMap_eq (D.boundaryLoop θ)
  have hbufferBd : ∀ z ∈ Set.range G.boundary, B ∈ 𝓝[Bd] z := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨θ, rfl⟩ := hβsurj x
    have hval : ((G.boundary (β θ) : (double 3 K).space) : F × F × ℝ) = ι (γ θ) := hβ θ
    have hz : π (G.boundary (β θ)) = (γ θ : F) := by
      change glueSnd F F ((G.boundary (β θ) : (double 3 K).space) : F × F × ℝ) = (γ θ : F)
      rw [hval]
      exact hπι _ (hγK θ)
    have hp : S.boundaryNeighborhood.space ∈ 𝓝[S.boundaryComplex.space] (γ θ : F) := by
      rw [hγproj θ]
      exact hbuffer (D.boundaryLoop θ) (D.boundaryLoop θ).property
    obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hp
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨π ⁻¹' V, ?_, ?_⟩
    · apply hπcont.continuousAt.preimage_mem_nhds
      rw [hz]
      exact hV
    · rintro w ⟨hwV, b, hb, hbw⟩
      have hπw : π w = b := by
        change glueSnd F F ((w : (double 3 K).space) : F × F × ℝ) = b
        rw [← hbw]
        exact hπι b (PiecewiseLinear.boundaryComplex_space_subset 3 K hb)
      refine ⟨b, hVsub ⟨?_, hb⟩, hbw⟩
      rw [← hπw]
      exact hwV
  obtain ⟨A, hA, -, hAside, hAbuffer, hAloop⟩ :=
    generalPosition S G β γ (Covering.isLocallyInjective_domRestrict_iff.mp hloc) hcard
      hBsub hbufferBd hinterBd hmapC hproperBd hβsurj hβ havoidγ
  obtain ⟨A', hA', -, hnonsingular, -, hside, -, hloop⟩ :=
    NormalSingularCellData.exists_complexity_eq_zero_of_descendingSurgery_of_motive
      (fun A₀ _ => MapsTo A₀ A₀.domain C ∧
        (∀ z ∈ Set.range A₀.boundary, B ∈ 𝓝[Bd] z) ∧
        ∃ (c : loopCircle ≃ₜ frontier A₀.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
          (∀ θ, ((A₀ (c θ) : (double 3 K).space) : F × F × ℝ) = ι (δ θ)) ∧
            ¬loopClassMeets δ S.basepoint S.normalSubgroup)
      (fun A₀ hA₀ hcomplexity hmotive =>
        descentStep S hor A₀ hA₀ hcomplexity hmotive.1 hmotive.2.1 hmotive.2.2)
      hA ⟨hAside, hAbuffer, hAloop⟩
  refine S.exists_embeddedDisk_of_nonsingular_two_cell_in_double A' hnonsingular ?_
    hA'.image_inter_boundary hloop
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact hside hx

end DifferentialGeometry.Topology.PiecewiseLinear
