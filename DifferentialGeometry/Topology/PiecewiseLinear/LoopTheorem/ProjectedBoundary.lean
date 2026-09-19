/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

/-!
# Boundary-relative embedded disks in a normal neighborhood
-/

open Set

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

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
