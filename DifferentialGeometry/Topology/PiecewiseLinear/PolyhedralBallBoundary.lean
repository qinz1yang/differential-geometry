/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem IsPolyhedralBall.polyhedralBoundary_eq_image_stdSimplexBoundary
    {P : Set X} (hP : IsPolyhedralBall (n := n) (m + 1) P) (T : PLPiece n X P)
    {f : (Fin (m + 2) → ℝ) → EuclideanSpace ℝ (Fin T.ambientDim)}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) T.piece.complex.space) :
    polyhedralBoundary (m + 1) P hP.isPolyhedralManifoldWithBoundary =
      (T.piece.map ∘ f) '' stdSimplexBoundary (m + 1) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  rw [polyhedralBoundary_eq_of_piece _ T,
    boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex T.piece.complex hf,
    simplexBoundary_stdVertices_space, image_comp]

theorem IsPolyhedralBall.exists_isPLHomeomorphOn_chart_image_boundary
    {P : Set X} (hP : IsPolyhedralBall (n := n) (m + 1) P)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hPe : P ⊆ e.source) :
    ∃ f : (Fin (m + 2) → ℝ) → EuclideanSpace ℝ (Fin n),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) (e '' P) ∧
        f '' stdSimplexBoundary (m + 1) =
          e '' polyhedralBoundary (m + 1) P hP.isPolyhedralManifoldWithBoundary := by
  obtain ⟨T, hT⟩ := hP
  have hP' : IsPolyhedralBall (n := n) (m + 1) P := ⟨T, hT⟩
  obtain ⟨f, hf⟩ := hT
  refine ⟨(e ∘ T.piece.map) ∘ f, hf.trans (T.piece.isPLHomeomorphOn_chart_image e he hPe), ?_⟩
  rw [hP'.polyhedralBoundary_eq_image_stdSimplexBoundary T hf]
  simp only [image_comp]

theorem IsPolyhedralBall.closure_sdiff_polyhedralBoundary [T2Space X]
    {P : Set X} (hP : IsPolyhedralBall (n := n) (m + 1) P) :
    closure (P \ polyhedralBoundary (m + 1) P hP.isPolyhedralManifoldWithBoundary) = P := by
  obtain ⟨T, hT⟩ := hP
  have hP' : IsPolyhedralBall (n := n) (m + 1) P := ⟨T, hT⟩
  obtain ⟨f, hf⟩ := hT
  have hJ : f '' stdSimplexBoundary (m + 1) ⊆ T.piece.complex.space :=
    image_subset_iff.mpr fun _ hx => hf.bijOn.mapsTo hx.1
  have hcl : closure (T.piece.complex.space \ f '' stdSimplexBoundary (m + 1)) ⊆
      T.piece.complex.space := closure_minimal sdiff_subset T.piece.isPolyhedron_space.isClosed
  have himg := image_closure_of_isCompact
    (T.piece.isPolyhedron_space.isCompact.of_isClosed_subset isClosed_closure hcl)
    (T.piece.continuousOn.mono hcl)
  rw [hf.closure_sdiff_image_stdSimplexBoundary] at himg
  rw [T.piece.bijOn.injOn.image_sdiff_subset hJ, T.piece.bijOn.image_eq, ← image_comp] at himg
  rw [hP'.polyhedralBoundary_eq_image_stdSimplexBoundary T hf]
  exact himg.symm

end DifferentialGeometry.Topology.PiecewiseLinear
