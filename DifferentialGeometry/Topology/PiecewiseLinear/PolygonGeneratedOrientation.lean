import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPolygonOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialWalkHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.WalkMonodromyHomotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

section Simplicial

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Geometry.SimplicialComplex ℝ F}

open Classical in
theorem SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow
    (ε : SimplicialBoolCocycle M) {v₀ u : M.vertices}
    (γ : (SimplicialComplex.edgeGraph M).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph M).Walk u u)
    (q : (SimplicialComplex.edgeGraph M).Walk u v₀) (k : ℕ)
    (hp : SimplicialHomotopic M p (q.append ((closedWalkPow γ k).append q.reverse))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_simplicialHomotopic hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkPow]
  rcases hx (k : ZMod 2) with hk | hk
  · exact Or.inl (by rw [hk, zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

end Simplicial

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
def IsSimpliciallyGeneratedByPolygon {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀) : Prop :=
  ∀ (u : (barycentricSubdivision L).vertices)
    (p : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u u),
    ∃ (q : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u v₀) (k : ℕ),
      SimplicialHomotopic (barycentricSubdivision L) p
        (q.append ((closedWalkPow γ k).append q.reverse))

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

open Classical in
theorem isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon
    (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : IsSimpliciallyGeneratedByPolygon γ)
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L := by
  refine isOrientable_of_ambient_nullHomotopic_polygon hLK hK hL o hconn γ (fun u p => ?_) hnull
  obtain ⟨q, k, hq⟩ := hgen u p
  exact SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow
    _ γ p q k hq

end DifferentialGeometry.Topology.PiecewiseLinear
