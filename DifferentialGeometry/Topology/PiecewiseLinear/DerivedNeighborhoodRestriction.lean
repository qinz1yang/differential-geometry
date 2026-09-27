/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem restrict_derivedNeighborhood_eq (K S L : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) :
    restrict (derivedNeighborhood K L) S.space = derivedNeighborhood S L := by
  ext u
  constructor
  · rintro ⟨⟨D, hD, hne, hmeet, rfl⟩, hconv⟩
    refine ⟨D, ?_, hne, hmeet, rfl⟩
    refine ⟨fun e he => ?_, hD.2⟩
    have heK := hD.mem_faces he
    have hcS : e.centroid ℝ id ∈ S.space :=
      hconv (subset_convexHull ℝ _ (Finset.mem_image_of_mem _ he))
    have hcS' : e.centroid ℝ id ∈ (barycentricSubdivision S).space :=
      (barycentricSubdivision_isSubdivision S).space_eq.symm.subset hcS
    exact mem_faces_of_mem_openSimplex_of_mem_space
      (barycentricSubdivision_faces_subset hS) heK
      (centroid_mem_openSimplex ((barycentricSubdivision K).nonempty_of_mem_faces heK)) hcS'
  · intro hu
    have huS := hu
    rcases hu with ⟨D, hD, hne, hmeet, rfl⟩
    refine ⟨⟨D, hD.of_le (barycentricSubdivision_faces_subset hS), hne, hmeet, rfl⟩, ?_⟩
    exact ((secondDerived S).convexHull_subset_space
      (derivedNeighborhood_faces_subset S L huS)).trans
        (secondDerived_isSubdivision S).space_eq.subset

open Classical in
theorem derivedNeighborhood_space_inter_subcomplex (K S L : Geometry.SimplicialComplex ℝ E)
    (hS : S.faces ⊆ K.faces) :
    (derivedNeighborhood K L).space ∩ S.space = (derivedNeighborhood S L).space := by
  rw [← (secondDerived_isSubdivision S).space_eq,
    ← restrict_space_eq_inter_of_faces_subset (secondDerived K) (derivedNeighborhood K L)
      (secondDerived S) (derivedNeighborhood_faces_subset K L)
      (secondDerived_faces_subset hS),
    (secondDerived_isSubdivision S).space_eq,
    restrict_derivedNeighborhood_eq K S L hS]

end DifferentialGeometry.Topology.PiecewiseLinear
