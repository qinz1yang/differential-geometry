/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.TwoSidedNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.isOrientable_of_finrank_eq_three
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) : IsOrientable 2 L := by
  obtain ⟨T, hT, hTcard, hLT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space L).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hLint : L.space ⊆ interior K.space := hLT.trans hint.symm.subset
  have hLK : L.space ⊆ K.space := hLint.trans interior_subset
  have hLB : Disjoint L.space (boundaryComplex 3 K).space := by
    apply disjoint_left.mpr
    intro x hxL hxB
    apply Set.disjoint_left.mp disjoint_interior_frontier (hLint hxL)
    rwa [frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
  have htwoAmbient : DifferentialGeometry.Topology.IsTwoSided L.space :=
    hL.isTwoSided L hdim hconn
  have htwo : DifferentialGeometry.Topology.IsTwoSided
      (((↑) : K.space → E) ⁻¹' L.space) :=
    htwoAmbient.preimage_of_isInducing Topology.IsInducing.subtypeVal (by
      rw [Subtype.range_val]
      exact subset_interior_iff_mem_nhdsSet.mp hLint)
  obtain ⟨N, A, B, hNfin, hAfin, hBfin, hN, hA, hB, hNconn, hAconn, hBconn,
    hNK, hNU, hNnhds, hNB, hAB, hABinter, hboundaryA, hboundaryB⟩ :=
    hK.exists_neighborhood_manifold_pair_of_twoSided hL hLK hLB hconn htwo
      (U := univ) Filter.univ_mem
  let _ : Finite N.faces := hNfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hAN : A.space ⊆ N.space := by
    intro x hx
    rw [← hAB]
    exact Or.inl hx
  have hAT : A.space ⊆ convexHull ℝ (T : Set E) := by
    rw [← hKspace]
    exact hAN.trans hNK
  have hAo : IsOrientable 3 A :=
    isOrientable_of_space_subset_convexHull A hA T hTcard hAT
  let D := boundaryComplex 3 A
  let _ : Finite D.faces := (boundaryComplex_faces_finite 3 A).to_subtype
  have hD : IsCombinatorialManifold 2 D := isCombinatorialManifold_boundaryComplex A hA
  have hDo : IsOrientable 2 D := hAo.boundary A hA
  have hLD : L.space ⊆ D.space := by
    rw [show D.space = L.space ∪ (A.space ∩ (boundaryComplex 3 N).space) from hboundaryA]
    exact subset_union_left
  obtain ⟨R, hR, hRfin, hRL⟩ := exists_isSubdivision_restrict_isSubdivision D L hLD
  let _ : Finite R.faces := hRfin.to_subtype
  let C := restrict R L.space
  let _ : Finite C.faces := (restrict_faces_finite R L.space).to_subtype
  have hRman : IsCombinatorialManifold 2 R := hD.of_isSubdivision hR
  have hCman : IsCombinatorialManifold 2 C := hL.of_isSubdivision hRL
  have hRo : IsOrientable 2 R := hDo.subdivision hD.isCombinatorialManifoldWithBoundary hR
  have hCo : IsOrientable 2 C := IsOrientable.of_le R C (restrict_faces_subset R L.space)
    hRman.isCombinatorialManifoldWithBoundary hCman.isCombinatorialManifoldWithBoundary hRo
  exact hCo.of_isSubdivision hL.isCombinatorialManifoldWithBoundary hRL

open Classical in
theorem IsCombinatorialManifold.isOrientable_euclidean_three
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space) :
    IsOrientable 2 L := by
  exact hL.isOrientable_of_finrank_eq_three L (by simp) hconn

end DifferentialGeometry.Topology.PiecewiseLinear
