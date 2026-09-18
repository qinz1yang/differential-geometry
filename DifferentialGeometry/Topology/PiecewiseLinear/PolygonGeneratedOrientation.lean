import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPolygonOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.WalkMonodromyHomotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_polygonGenerated
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

open Classical in
def IsGeneratedByPolygon {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀) : Prop :=
  ∀ (u : (barycentricSubdivision L).vertices)
    (p : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u u),
    ∃ (q : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u v₀) (k : ℕ),
      (walkPath p).Homotopic (walkPath (q.append ((closedWalkPow γ k).append q.reverse)))

open Classical in
theorem isOrientable_of_ambient_nullHomotopic_generated_polygon (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : IsGeneratedByPolygon γ)
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L := by
  refine isOrientable_of_ambient_nullHomotopic_polygon hLK hK hL o hconn γ (fun u p => ?_) hnull
  obtain ⟨q, k, hq⟩ := hgen u p
  exact SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_pow _ γ p q k hq

end DifferentialGeometry.Topology.PiecewiseLinear
