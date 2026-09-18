import DifferentialGeometry.Topology.PiecewiseLinear.ContractiblePolygonOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexOrientationCocycle

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E}

open Classical in
def edgeGraphHom (hLK : L.faces ⊆ K.faces) :
    SimplicialComplex.edgeGraph L →g SimplicialComplex.edgeGraph K where
  toFun v := ⟨(v : E), hLK v.2⟩
  map_rel' h :=
    ⟨fun he => h.1 (Subtype.ext (congrArg (fun z : K.vertices => (z : E)) he)), hLK h.2⟩

open Classical in
theorem edgeGraphHom_apply (hLK : L.faces ⊆ K.faces) (v : L.vertices) :
    ((edgeGraphHom hLK v : K.vertices) : E) = (v : E) := rfl

open Classical in
theorem walkMonodromy_ofLe (ε : SimplicialBoolCocycle K) (hLK : L.faces ⊆ K.faces)
    {u w : L.vertices} (p : (SimplicialComplex.edgeGraph L).Walk u w) :
    (ε.ofLe hLK).walkMonodromy p = ε.walkMonodromy (p.map (edgeGraphHom hLK)) := by
  induction p with
  | nil => rw [Walk.map_nil, (ε.ofLe hLK).walkMonodromy_nil, ε.walkMonodromy_nil]
  | cons h q ih =>
      rw [Walk.map_cons, (ε.ofLe hLK).walkMonodromy_cons, ε.walkMonodromy_cons, ih]
      rfl

variable [FiniteDimensional ℝ E] [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_ambientPolygon
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

open Classical in
theorem isOrientable_of_ambient_nullHomotopic_polygon (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : ∀ (u : (barycentricSubdivision L).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u u),
      ((orientationCocycle hK o).ofLe
          (barycentricSubdivision_faces_subset hLK)).walkMonodromy p = 0 ∨
        ((orientationCocycle hK o).ofLe
            (barycentricSubdivision_faces_subset hLK)).walkMonodromy p =
          ((orientationCocycle hK o).ofLe
            (barycentricSubdivision_faces_subset hLK)).walkMonodromy γ)
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L := by
  refine isOrientable_of_isCoboundary_ofLe hLK hK hL o ?_
  refine ((orientationCocycle hK o).ofLe
    (barycentricSubdivision_faces_subset hLK)).isCoboundary_of_walkMonodromy_generated
      hconn γ hgen ?_
  rw [walkMonodromy_ofLe]
  exact (orientationCocycle hK o).walkMonodromy_eq_zero_of_homotopic_refl _ hnull

end DifferentialGeometry.Topology.PiecewiseLinear
