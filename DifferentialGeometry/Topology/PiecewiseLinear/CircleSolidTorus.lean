/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLSphere.exists_solid_torus_neighborhood {J : Set E} (hJ : IsPLSphere 1 J)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ (N : Geometry.SimplicialComplex ℝ E) (f : (Fin 3 → ℝ) × ℝ → E),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧ J ⊆ interior N.space ∧
      IsTopologicalSolidTorus N.space ∧
      IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N.space ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) := by
  obtain ⟨L, hLfin, hLsp⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hT, hTcard, hJT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    hJ.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKsp : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKsp.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hJK : J ⊆ interior K.space := by
    rw [hKsp, interior_convexHull_eq_openSimplex hT (by omega)]
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
  obtain ⟨f, hf, hends⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends
    R C hRball.isCombinatorialManifoldWithBoundary (restrict_faces_subset R L.space)
    hC.isCombinatorialManifold hC.isConnected (isOrientable_of_isPLBall hRball)
  refine ⟨derivedNeighborhood R C, f, derivedNeighborhood_faces_finite R C,
    hRball.isCombinatorialManifoldWithBoundary.derivedNeighborhood C, ?_,
    hf.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hends, hf, hends⟩
  intro x hx
  have hRx : R.space ∈ 𝓝 x := by
    rw [hRspace]
    exact mem_interior_iff_mem_nhds.mp (hJK hx)
  have hNx := derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset R L.space)
    (hCsp.symm.subset hx)
  rw [nhdsWithin_eq_nhds.mpr hRx] at hNx
  exact mem_interior_iff_mem_nhds.mpr hNx

end DifferentialGeometry.Topology.PiecewiseLinear
