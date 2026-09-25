import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidTorusFilling
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLTorus.exists_manifold_filling_in_solid_torus
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T)
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hsolid : IsTopologicalSolidTorus K.space) (hTK : T ⊆ K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      frontier R.space = T ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧ R.space ⊆ K.space := by
  obtain ⟨L, hLfin, hL, hLc, hLspace⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨R, hRfin, hR, -, hfront, hreg, hint, hext⟩ :=
    hL.exists_isCombinatorialManifoldWithBoundary_boundaryComplex L (by simp) hLc
  let _ : Finite R.faces := hRfin.to_subtype
  have hRT : frontier R.space = T := hfront.trans hLspace
  refine ⟨R, hRfin, hR, hRT, hreg, hint, hext, ?_⟩
  exact DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    (isPolyhedron_space R).isCompact (isPolyhedron_space K).isCompact
    (hsolid.isConnected_compl_of_combinatorial_manifold hK).isPreconnected (hRT ▸ hTK)

theorem IsPLTorus.exists_manifold_filling_in_solid_torus_interior
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T)
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hsolid : IsTopologicalSolidTorus K.space) (hTK : T ⊆ interior K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      frontier R.space = T ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧ IsConnected R.spaceᶜ ∧
      R.space ⊆ interior K.space := by
  obtain ⟨R, hRfin, hR, hfront, hreg, hint, hext, hRK⟩ :=
    hT.exists_manifold_filling_in_solid_torus hK hsolid (hTK.trans interior_subset)
  refine ⟨R, hRfin, hR, hfront, hreg, hint, hext, ?_⟩
  intro x hx
  by_cases hxi : x ∈ interior R.space
  · exact interior_mono hRK hxi
  · exact hTK (hfront ▸ And.intro (subset_closure hx) hxi)

end DifferentialGeometry.Topology.PiecewiseLinear
