import DifferentialGeometry.Topology.PiecewiseLinear.CocycleWalkLift
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonNeighborhoodOrientation

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_contractiblePolygon
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

open Classical in
theorem isOrientable_of_nullHomotopic_polygon
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    {v₀ : (barycentricSubdivision K).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk v₀ v₀)
    (hgen : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p = 0 ∨
        (orientationCocycle hK o).walkMonodromy p =
          (orientationCocycle hK o).walkMonodromy γ)
    (hnull : (walkPath γ).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K) v₀))) :
    IsOrientable n K :=
  isOrientable_of_polygon_walkMonodromy_eq_zero hK o hconn γ hgen
    ((orientationCocycle hK o).walkMonodromy_eq_zero_of_homotopic_refl γ hnull)

open Classical in
theorem isOrientable_of_forall_nullHomotopic_walk
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    (hnull : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (walkPath p).Homotopic (Path.refl (vertexPoint (barycentricSubdivision K) u))) :
    IsOrientable n K :=
  isOrientable_of_forall_walkMonodromy_eq_zero hK o hconn fun u p =>
    (orientationCocycle hK o).walkMonodromy_eq_zero_of_homotopic_refl p (hnull u p)

end DifferentialGeometry.Topology.PiecewiseLinear
