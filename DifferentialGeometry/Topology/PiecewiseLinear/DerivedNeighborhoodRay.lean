/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def derivedNeighborhoodRay (A K : Geometry.SimplicialComplex ℝ E)
    [Finite A.faces] : (frontier (derivedNeighborhood A K).space × Set.Ioo (0 : ℝ) 1) → E :=
  fun p => (1 - (p.2 : ℝ)) • (p.1 : E) + (p.2 : ℝ) •
    subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) p.1

open Classical in
theorem continuous_derivedNeighborhoodRay [FiniteDimensional ℝ E]
    (A K : Geometry.SimplicialComplex ℝ E) [Finite A.faces] :
    Continuous (derivedNeighborhoodRay A K) := by
  let _ : Finite (derivedNeighborhood A K).faces :=
    (derivedNeighborhood_faces_finite A K).to_subtype
  have hclosed : IsClosed (derivedNeighborhood A K).space :=
    (SimplicialComplex.isCompact_geometricSpace (derivedNeighborhood A K)).isClosed
  have hfront : frontier (derivedNeighborhood A K).space ⊆
      (derivedNeighborhood A K).space := hclosed.frontier_subset
  have hp : Continuous (fun x : frontier (derivedNeighborhood A K).space =>
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) x) :=
    (continuousOn_subcomplexBarycentricProjection_derivedNeighborhood.mono hfront).domRestrict
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
    (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_snd).smul (hp.comp continuous_fst))

end DifferentialGeometry.Topology.PiecewiseLinear
