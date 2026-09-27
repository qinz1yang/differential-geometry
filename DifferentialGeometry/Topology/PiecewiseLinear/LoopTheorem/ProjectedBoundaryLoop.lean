/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedCellInDouble

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem EmbeddedDisk.exists_boundaryLoop_lift {S : NormalSystem E} (D : EmbeddedDisk S) :
    ∃ β : ContinuousMap loopCircle (frontier D.domain), Function.Surjective β ∧
      ∀ θ, D.map (β θ) = (D.boundaryLoop θ : E) := by
  have hfront : frontier D.domain ⊆ D.domain :=
    D.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
  let _ : CompactSpace (frontier D.domain) :=
    isCompact_iff_compactSpace.mp
      (D.isPLBall_domain.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier hfront)
  let b : frontier D.domain → E := fun x => D.map x
  have hb : Continuous b :=
    (D.isPLHomeomorphOn.isPiecewiseAffineOn.continuousOn.mono hfront).domRestrict
  have hbinj : Function.Injective b := fun x y hxy =>
    Subtype.ext (D.isPLHomeomorphOn.bijOn.injOn (hfront x.property) (hfront y.property) hxy)
  let e : (frontier D.domain) ≃ₜ range b := (hb.isClosedEmbedding hbinj).isEmbedding.toHomeomorph
  have hγ (θ : loopCircle) : (D.boundaryLoop θ : E) ∈ range b := by
    obtain ⟨x, hx, hxeq⟩ := D.boundary_range.subset ⟨θ, rfl⟩
    exact ⟨⟨x, hx⟩, hxeq⟩
  let γ : ContinuousMap loopCircle (range b) :=
    ⟨fun θ => ⟨D.boundaryLoop θ, hγ θ⟩,
      (continuous_subtype_val.comp D.boundaryLoop.continuous).subtype_mk _⟩
  let β : ContinuousMap loopCircle (frontier D.domain) :=
    (e.symm : ContinuousMap (range b) (frontier D.domain)).comp γ
  have hβ (θ : loopCircle) : D.map (β θ) = (D.boundaryLoop θ : E) :=
    congrArg Subtype.val (e.apply_symm_apply (γ θ))
  refine ⟨β, ?_, hβ⟩
  intro x
  obtain ⟨θ, hθ⟩ := D.boundary_range.superset ⟨x, x.property, rfl⟩
  refine ⟨θ, Subtype.ext ?_⟩
  exact D.isPLHomeomorphOn.bijOn.injOn (hfront (β θ).property) (hfront x.property)
    ((hβ θ).trans hθ)

variable [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_projected_singular_two_cell_with_boundaryLoop_lift
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)) (β : ContinuousMap loopCircle (frontier G.domain)),
      G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
      EqOn (fun x => (G x : E × E × ℝ)) (ι ∘ R.projection ∘ D.map) D.domain ∧
      MapsTo G G.domain C ∧ G.domain ∩ G ⁻¹' frontier C = frontier G.domain ∧
      IsLocallyInjective (G.domain.domRestrict G) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
      Function.Surjective β ∧ ∀ θ, (G (β θ) : E × E × ℝ) = ι (γ θ : E) := by
  classical
  intro K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  obtain ⟨G, γ, q, hdom, hγ, hGeq, hmap, hfront, hpre, -, -, havoid,
    -, hloc, hcard, -⟩ := R.exists_projected_singular_two_cell_in_double D
  obtain ⟨α, hαsurj, hα⟩ := D.exists_boundaryLoop_lift
  let e : (frontier D.domain) ≃ₜ frontier G.domain :=
    Homeomorph.setCongr (congrArg frontier hdom.symm)
  let β : ContinuousMap loopCircle (frontier G.domain) :=
    (e : ContinuousMap (frontier D.domain) (frontier G.domain)).comp α
  have hproper : G.domain ∩ G ⁻¹' frontier C = frontier G.domain := by
    rw [hfront]
    exact hpre
  refine ⟨G, γ, q, β, hdom, hγ, hGeq, hmap, hproper, hloc, hcard, havoid,
    e.surjective.comp hαsurj, ?_⟩
  intro θ
  have hx : (α θ : EuclideanSpace ℝ (Fin 2)) ∈ D.domain :=
    D.isPLBall_domain.isPolyhedron.isClosed.frontier_subset (α θ).property
  change (G (α θ) : E × E × ℝ) = ι (γ θ : E)
  refine (hGeq hx).trans ?_
  change ι (R.projection (D.map (α θ))) = ι (γ θ : E)
  rw [hα θ, hγ]
  exact congrArg ι (R.boundaryMap_eq (D.boundaryLoop θ)).symm

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
