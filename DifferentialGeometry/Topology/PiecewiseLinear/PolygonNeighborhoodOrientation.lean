/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CocycleMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.OrientationCocycle
import DifferentialGeometry.Topology.SimplicialComplex.EdgeConnectivity

namespace DifferentialGeometry.Topology.PiecewiseLinear

open SimpleGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_polygonNeighborhood
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

open Classical in
omit [FiniteDimensional ℝ E] in
theorem edgeGraph_barycentricSubdivision_preconnected
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (h : IsPreconnected K.space) :
    (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected := by
  refine edgeGraph_preconnected_of_isPreconnected_space (barycentricSubdivision K) ?_
  rw [(barycentricSubdivision_isSubdivision K).space_eq]
  exact h

open Classical in
theorem isOrientable_of_forall_walkMonodromy_eq_zero
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    (hzero : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p = 0) :
    IsOrientable n K :=
  (orientationCocycle_isCoboundary_iff hK o).mp
    ((orientationCocycle hK o).isCoboundary_of_preconnected hconn hzero)

open Classical in
theorem walkMonodromy_orientationCocycle_eq_zero_of_isOrientable
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (h : IsOrientable n K) {u : (barycentricSubdivision K).vertices}
    (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u) :
    (orientationCocycle hK o).walkMonodromy p = 0 :=
  (orientationCocycle hK o).walkMonodromy_eq_zero_of_isCoboundary
    ((orientationCocycle_isCoboundary_iff hK o).mpr h) p

open Classical in
theorem isOrientable_iff_forall_walkMonodromy_eq_zero
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected) :
    IsOrientable n K ↔ ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p = 0 :=
  ⟨fun h _ p => walkMonodromy_orientationCocycle_eq_zero_of_isOrientable hK o h p,
    fun hzero => isOrientable_of_forall_walkMonodromy_eq_zero hK o hconn hzero⟩

open Classical in
theorem isOrientable_of_polygon_walkMonodromy_eq_zero
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
    (hγ : (orientationCocycle hK o).walkMonodromy γ = 0) :
    IsOrientable n K :=
  (orientationCocycle_isCoboundary_iff hK o).mp
    ((orientationCocycle hK o).isCoboundary_of_walkMonodromy_generated hconn γ hgen hγ)

open Classical in
theorem exists_walkMonodromy_ne_zero_of_not_isOrientable
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    (h : ¬ IsOrientable n K) :
    ∃ (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
      (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p ≠ 0 := by
  let o (s : Finset E) (hs : s ∈ K.faces) : CoherentOrientation n (faceStarComplex K s) :=
    Classical.choice (isOrientable_faceStarComplex hK hs)
  refine ⟨o, ?_⟩
  by_contra hall
  refine h (isOrientable_of_forall_walkMonodromy_eq_zero hK o hconn fun u p => ?_)
  by_contra hp
  exact hall ⟨u, p, hp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
