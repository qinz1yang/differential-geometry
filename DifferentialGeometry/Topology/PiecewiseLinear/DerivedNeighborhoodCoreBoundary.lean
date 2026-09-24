/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

/-! # Derived Neighborhood Core Boundary -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) (hLK : L.faces ⊆ K.faces) :
    Disjoint L.space (boundaryComplex (n + 1) (derivedNeighborhood K L)).space := by
  classical
  have : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  apply disjoint_left.mpr
  intro x hxL hxB
  have hnhds := derivedNeighborhood_mem_nhdsWithin hLK hxL
  have hxN : x ∈ (derivedNeighborhood K L).space :=
    mem_of_mem_nhdsWithin (space_mono_of_faces_subset hLK hxL) hnhds
  have hx := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K
    (derivedNeighborhood K L) hK.isCombinatorialManifoldWithBoundary
    (hK.isCombinatorialManifoldWithBoundary.derivedNeighborhood L)
    (derivedNeighborhood_space_subset K L) hxN hnhds).mp hxB
  rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K] at hx
  simp at hx

end DifferentialGeometry.Topology.PiecewiseLinear
