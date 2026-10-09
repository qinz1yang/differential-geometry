/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance euclideanDecidableEq : DecidableEq E3 :=
  fun a b => Classical.propDecidable (a = b)

open Classical in
theorem isEmbedding_derivedNeighborhoodRay (A K : Geometry.SimplicialComplex ℝ E3)
    [Finite A.faces] (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hKA : K.faces ⊆ A.faces) (hKint : K.space ⊆ interior A.space) :
    _root_.Topology.IsEmbedding (derivedNeighborhoodRay A K) :=
  isEmbedding_derivedNeighborhoodRay_of_subset_interior A K hKA
    (derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint)

open Classical in
theorem range_derivedNeighborhoodRay (A K : Geometry.SimplicialComplex ℝ E3)
    [Finite A.faces] (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hKA : K.faces ⊆ A.faces) (hKint : K.space ⊆ interior A.space) :
    Set.range (derivedNeighborhoodRay A K) =
      interior (derivedNeighborhood A K).space \ K.space :=
  range_derivedNeighborhoodRay_of_subset_interior A K hKA
    (derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint)

end DifferentialGeometry.Topology.PiecewiseLinear
