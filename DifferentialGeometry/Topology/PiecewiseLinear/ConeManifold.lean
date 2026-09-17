import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRegion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsConeBase.isPLBall_of_apex_mem_frontier {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hM : IsCombinatorialManifoldWithBoundary (n + 1) (coneComplex hL))
    (hp : p ∈ frontier (coneComplex hL).space) : IsPLBall n L.space := by
  classical
  let _ : Finite (coneComplex hL).faces := (coneComplex_faces_finite hL (Set.toFinite L.faces)).to_subtype
  have hlink : SimplicialComplex.geometricLink (coneComplex hL) {p} = L :=
    Geometry.SimplicialComplex.ext (geometricLink_coneComplex_faces hL)
  have hpB : p ∈ (boundaryComplex (n + 1) (coneComplex hL)).space := by
    rwa [← frontier_space_eq_boundaryComplex_space_of_finrank hdim (coneComplex hL) hM]
  rw [← hlink]
  exact (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
    (coneComplex hL) (coneComplex hL) hM (IsSubdivision.refl _) (Or.inr (Or.inl rfl))).mpr hpB

open Classical in
theorem IsConeBase.isPLBall_of_isPLSphere_frontier
    (hdim : Module.finrank ℝ E = 3) {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hreg : closure (interior (coneComplex hL).space) = (coneComplex hL).space)
    (hS : IsPLSphere 2 (frontier (coneComplex hL).space))
    (hp : p ∈ frontier (coneComplex hL).space) : IsPLBall 2 L.space := by
  classical
  let _ : Finite (coneComplex hL).faces := (coneComplex_faces_finite hL (Set.toFinite L.faces)).to_subtype
  exact hL.isPLBall_of_apex_mem_frontier hdim
    (isCombinatorialManifoldWithBoundary_of_isPLSphere_frontier (coneComplex hL) hdim hreg hS) hp

end DifferentialGeometry.Topology.PiecewiseLinear
