/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoubleCoverProjection
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLocalEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem NonsingularCell.exists_isPLHomeomorphOn_eqOn_boundary
    {S : NormalSystem E} (D : NonsingularCell S) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → E,
      IsPLHomeomorphOn f D.sourceComplex.space (f '' D.sourceComplex.space) ∧
      MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      EqOn f (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space) ∧
      D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space = frontier D.sourceComplex.space ∧
      f '' D.sourceComplex.space ∩ S.boundaryComplex.space = f '' frontier D.sourceComplex.space ∧
      range (fun θ => (D.boundaryLoop θ : E)) = f '' frontier D.sourceComplex.space := by
  let _ : Finite D.sourceComplex.faces := D.finite_source.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hfront : frontier D.sourceComplex.space ⊆ D.sourceComplex.space :=
    frontier_subset_closure.trans (isPolyhedron_space D.sourceComplex).isClosed.closure_eq.subset
  have hmap := simplicialMap_mapsTo D.sourceComplex S.manifoldComplex D.vertexMap D.source_faces_map
  have hb : MapsTo (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space)
      (PiecewiseLinear.boundaryComplex 3 S.manifoldComplex).space := by
    intro x hx
    have hrange : simplicialMap D.sourceComplex D.vertexMap x ∈
        range (fun θ => (D.boundaryLoop θ : E)) := D.boundary_range.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨θ, hθ⟩ := hrange
    rw [← hθ]
    exact derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (D.boundaryLoop θ).2
  obtain ⟨f, hf, hfmap, hfix, hpre, hinter⟩ :=
    S.isManifold.exists_isPLHomeomorphOn_eqOn_preimage_boundary S.manifoldComplex
      (isPolyhedron_space D.sourceComplex) D.source_isPLBall.isPLSphere_frontier.isPolyhedron
      hfront (isPiecewiseAffineOn_simplicialMap D.sourceComplex D.vertexMap) D.nonsingular hmap hb
  have himage := hfix.image_eq
  exact ⟨f, hf, hfmap, hfix, hpre, hinter.trans himage.symm,
    D.boundary_range.trans himage.symm⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.preimage_boundaryComplex_subset
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T) :
    T.manifoldComplex.space ∩ R.projection ⁻¹' S.boundaryComplex.space ⊆
      T.boundaryComplex.space := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ : Finite T.manifoldComplex.faces := T.manifoldComplex_faces_finite.to_subtype
  have hpl := R.isPiecewiseAffineOn_projection.mono_of_isPolyhedron
    (isPolyhedron_space T.manifoldComplex) T.manifoldComplex_space_subset_ambient
  obtain ⟨hloc, -⟩ := Covering.locally_injective_fiber_le_of_isCoveringMap_restrict
    R.isCoveringMap (fun _ => rfl) (continuous_id.continuousOn (s := T.manifoldComplex.space))
    (Function.injective_id.injOn) T.manifoldComplex_space_subset_ambient
    (fun y => (R.fiber_card y).le)
  exact hpl.preimage_boundaryComplex_subset_of_isLocallyInjective T.manifoldComplex
    S.manifoldComplex T.isManifold S.isManifold
    (R.projection_mapsTo.mono_left T.manifoldComplex_space_subset_ambient)
    (Covering.isLocallyInjective_domRestrict_iff.mpr hloc)

open Classical in
theorem DoubleCoverDiagram.exists_projected_disk_with_boundary
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : NonsingularCell T) :
    ∃ (g : EuclideanSpace ℝ (Fin 2) → F) (f : EuclideanSpace ℝ (Fin 2) → E)
      (γ : freeLoop S.boundaryNeighborhoodSpace) (q : Path S.basepoint (γ 0)),
      IsPLHomeomorphOn g D.sourceComplex.space (g '' D.sourceComplex.space) ∧
      MapsTo g D.sourceComplex.space T.manifoldComplex.space ∧
      EqOn g (simplicialMap D.sourceComplex D.vertexMap) (frontier D.sourceComplex.space) ∧
      f = R.projection ∘ g ∧ IsPiecewiseAffineOn f D.sourceComplex.space ∧
      MapsTo f D.sourceComplex.space S.manifoldComplex.space ∧
      (∀ x ∈ D.sourceComplex.space, ∃ U ∈ 𝓝[D.sourceComplex.space] x, InjOn f U) ∧
      (∀ y, (D.sourceComplex.space ∩ f ⁻¹' {y}).encard ≤ 2) ∧
      D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space = frontier D.sourceComplex.space ∧
      f '' D.sourceComplex.space ∩ S.boundaryComplex.space = f '' frontier D.sourceComplex.space ∧
      range (fun θ => (γ θ : E)) = f '' frontier D.sourceComplex.space ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup := by
  obtain ⟨g, hg, hgmap, hgfix, hgpre, -, -⟩ := D.exists_isPLHomeomorphOn_eqOn_boundary
  obtain ⟨f, γ, q, hfg, hf, hfmap, hloc, htwo, hboundary, havoid⟩ :=
    R.exists_projected_disk_of_embedding D hg.isPiecewiseAffineOn hg.bijOn.injOn hgmap hgfix
  have hfront : frontier D.sourceComplex.space ⊆ D.sourceComplex.space :=
    frontier_subset_closure.trans D.source_isPLBall.isPolyhedron.isClosed.closure_eq.subset
  have hfb : MapsTo f (frontier D.sourceComplex.space) S.boundaryComplex.space := by
    intro x hx
    obtain ⟨θ, hθ⟩ := hboundary.symm.subset ⟨x, hx, rfl⟩
    rw [← hθ]
    exact derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).2
  have hpre : D.sourceComplex.space ∩ f ⁻¹' S.boundaryComplex.space =
      frontier D.sourceComplex.space := by
    apply Subset.antisymm
    · rintro x ⟨hx, hfx⟩
      have hgx : g x ∈ T.boundaryComplex.space :=
        R.preimage_boundaryComplex_subset ⟨hgmap hx, by
          simpa only [mem_preimage, hfg, Function.comp_apply] using hfx⟩
      exact hgpre.subset ⟨hx, hgx⟩
    · exact fun x hx => ⟨hfront hx, hfb hx⟩
  refine ⟨g, f, γ, q, hg, hgmap, hgfix, hfg, hf, hfmap, hloc, htwo, hpre, ?_, hboundary, havoid⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hfx⟩
    exact ⟨x, hpre.subset ⟨hx, hfx⟩, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hfront hx, rfl⟩, hfb hx⟩
end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
