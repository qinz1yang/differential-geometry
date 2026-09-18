import DifferentialGeometry.Topology.PiecewiseLinear.PolygonGeneratedOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.WalkPathConcatenation

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_fromLoops
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

omit [FiniteDimensional ℝ E] [Finite L.faces] in
open Classical in
theorem isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : ∀ ℓ : Path (vertexPoint (barycentricSubdivision L) v₀)
        (vertexPoint (barycentricSubdivision L) v₀),
      ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k)) :
    IsGeneratedByPolygon γ :=
  fun u p => exists_zpow_conjugate_homotopic_walkPath hconn γ hgen u p

open Classical in
theorem isOrientable_of_ambient_nullHomotopic_loop_generated_polygon
    (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : ∀ ℓ : Path (vertexPoint (barycentricSubdivision L) v₀)
        (vertexPoint (barycentricSubdivision L) v₀),
      ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k))
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L :=
  isOrientable_of_ambient_nullHomotopic_generated_polygon hLK hK hL o hconn γ
    (isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow hconn γ hgen) hnull

end DifferentialGeometry.Topology.PiecewiseLinear
