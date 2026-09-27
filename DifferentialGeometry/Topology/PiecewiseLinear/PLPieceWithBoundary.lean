/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

structure PLPieceWithBoundary (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (S Bd : Set X) where
  piece : PLPieceIn E n X S
  boundaryComplex : Geometry.SimplicialComplex ℝ E
  boundary_faces : boundaryComplex.faces ⊆ piece.complex.faces
  boundary_image : piece.map '' boundaryComplex.space = Bd
  source_compact : IsCompact S
  source_manifold : IsCombinatorialManifoldWithBoundary n piece.complex

namespace PLPieceWithBoundary

theorem boundary_subset_source {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S Bd : Set X}
    (T : PLPieceWithBoundary E n X S Bd) : Bd ⊆ S := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := T.boundary_image.symm.subset hy
  exact T.piece.bijOn.mapsTo (space_mono_of_faces_subset T.boundary_faces hx)

theorem boundary_image_subset_source {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S Bd : Set X}
    (T : PLPieceWithBoundary E n X S Bd) :
    T.piece.map '' T.boundaryComplex.space ⊆ S := by
  rw [T.boundary_image]
  exact T.boundary_subset_source

theorem boundary_faces_subset_source_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S Bd : Set X}
    (T : PLPieceWithBoundary E n X S Bd) :
    T.boundaryComplex.faces ⊆ T.piece.complex.faces :=
  T.boundary_faces

end PLPieceWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
