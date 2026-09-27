/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSpine
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CircleSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexRefinement
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable local instance markedCircleTorusDecidableEq :
    DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _

open Classical in
theorem isSpine_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space)
    (hinterior : ∀ s ∈ L.faces, s ∉ (boundaryComplex 3 K).faces)
    (hor : IsOrientable 3 K) : IsSpine (derivedNeighborhood K L).space L.space := by
  obtain ⟨T, hT, hTcard, h0T⟩ := exists_affineIndependent_openSimplex_superset 2
    (by simp) (isCompact_singleton.isBounded :
      Bornology.IsBounded ({0} : Set (EuclideanSpace ℝ (Fin 2))))
  have hP := isHPolytope_convexHull_of_affineIndependent T hT
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (convexHull ℝ (T : Set _)) := by
    rw [interior_convexHull_eq_openSimplex hT (by simpa using hTcard)]
    exact h0T (mem_singleton _)
  obtain ⟨φ, hφ, hends, haxis⟩ :=
    exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends_marked K L hK hLK hL
      hconn hinterior hor hP h0
  rw [← haxis]
  exact hφ.isSpine_of_eq_ends (by simpa using hP.isPLBall ⟨0, h0⟩) hends h0

open Classical in
theorem IsPLSphere.exists_solid_torus_neighborhood_with_spine_subset_of_isOpen
    {J O : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsPLSphere 1 J)
    (hO : IsOpen O) (hJO : J ⊆ O) :
    ∃ N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
      N.space ⊆ O ∧ J ⊆ interior N.space ∧ IsSpine N.space J := by
  obtain ⟨L, hLfin, hLsp⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hT, hTcard, hJT⟩ := exists_affineIndependent_openSimplex_superset 3
    (by simp) hJ.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKsp : K.space = convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKsp.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hJK : J ⊆ interior K.space := by
    rw [hKsp, interior_convexHull_eq_openSimplex hT (by simpa using hTcard)]
    exact hJT
  have hLK : L.space ⊆ K.space := hLsp.subset.trans (hJK.trans interior_subset)
  obtain ⟨R, hRfin, hRsp, -, hRL⟩ := exists_simplicialComplex_space_union K L
  let _ : Finite R.faces := hRfin.to_subtype
  have hRspace : R.space = K.space := hRsp.trans (union_eq_self_of_subset_right hLK)
  have hRball : IsPLBall 3 R.space := hRspace.symm ▸ hKball
  let C := restrict R L.space
  let _ : Finite C.faces := (restrict_faces_finite R L.space).to_subtype
  have hCsp : C.space = J := hRL.space_eq.trans hLsp
  have hC : IsPLSphere 1 C.space := hCsp.symm ▸ hJ
  have hCR := restrict_faces_subset R L.space
  obtain ⟨R', hR', hR'fin, hCR', hsmall⟩ :=
    exists_isSubdivision_regularNeighborhoodIn_subset_of_isOpen R C hCR hO
      (hCsp.subset.trans hJO)
  let _ : Finite R'.faces := hR'fin.to_subtype
  have hR'ball : IsPLBall 3 R'.space := hR'.space_eq.symm ▸ hRball
  have hman := hR'ball.isCombinatorialManifoldWithBoundary
  have hCint : C.space ⊆ interior R'.space := by
    rw [hCsp, hR'.space_eq, hRspace]
    exact hJK
  have hinterior : ∀ s ∈ C.faces, s ∉ (boundaryComplex 3 R').faces := by
    intro s hs
    apply hman.notMem_boundaryComplex_faces_of_forall_mem_interior (by simp) (hCR' hs)
    intro v hv
    exact hCint (C.convexHull_subset_space hs (subset_convexHull ℝ _ hv))
  refine ⟨derivedNeighborhood R' C, derivedNeighborhood_faces_finite R' C,
    hman.derivedNeighborhood C, ?_, ?_, ?_⟩
  · apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst x hx
    exact hsmall ((regularNeighborhoodIn R' C.space).convexHull_subset_space
      ⟨ht, t, ht, Finset.Subset.refl t, s.centroid ℝ id, hst,
        C.convexHull_subset_space hs (s.centroid_mem_convexHull
          (C.nonempty_of_mem_faces hs))⟩ hx)
  · intro x hx
    have hRx : R'.space ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hCint (hCsp.symm ▸ hx))
    have hNx := derivedNeighborhood_mem_nhdsWithin hCR' (hCsp.symm ▸ hx)
    rw [nhdsWithin_eq_nhds.mpr hRx] at hNx
    exact mem_interior_iff_mem_nhds.mpr hNx
  · rw [← hCsp]
    exact isSpine_derivedNeighborhood_circle R' C hman hCR' hC.isCombinatorialManifold
      hC.isConnected hinterior (isOrientable_of_isPLBall hR'ball)

theorem IsPLSphere.exists_solid_torus_neighborhood_with_spine
    {J : Set (EuclideanSpace ℝ (Fin 3))} (hJ : IsPLSphere 1 J) :
    ∃ N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
      J ⊆ interior N.space ∧ IsSpine N.space J := by
  obtain ⟨N, hfin, hN, -, hJint, hspine⟩ :=
    hJ.exists_solid_torus_neighborhood_with_spine_subset_of_isOpen isOpen_univ (subset_univ _)
  exact ⟨N, hfin, hN, hJint, hspine⟩

end DifferentialGeometry.Topology.PiecewiseLinear
