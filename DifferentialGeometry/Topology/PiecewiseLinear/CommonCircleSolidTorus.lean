/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCommonAnnularDerivedNeighborhood.exists_solid_torus
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hor : IsOrientable 3 K)
    (hJ : IsPLSphere 1 J) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (f : (Fin 3 → ℝ) × ℝ → E),
      P.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 P ∧ P.space = N ∧
      IsTopologicalSolidTorus N ∧ IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) := by
  obtain ⟨R, L, P₀, -, hRfin, hLfin, -, -, hRK, hLspace, -, -, hP₀R, -, hLP₀,
    -, hN, -⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hR := hK.of_isSubdivision hRK
  have hL : IsPLSphere 1 L.space := hLspace.symm ▸ hJ
  obtain ⟨f, hf, hends⟩ := exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends
    R L hR (hLP₀.trans hP₀R) hL.isCombinatorialManifold hL.isConnected
    (hor.subdivision hK hRK)
  exact ⟨derivedNeighborhood R L, f, derivedNeighborhood_faces_finite R L,
    hR.derivedNeighborhood L, hN,
    hN ▸ hf.isTopologicalSolidTorus_of_eq_ends (isPLBall_stdSimplex 2) hends,
    hN ▸ hf, hends⟩

omit [FiniteDimensional ℝ E] in
theorem IsCommonAnnularDerivedNeighborhood.subset_interior
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁) (hJK : J ⊆ interior K.space) :
    J ⊆ interior N := by
  obtain ⟨O, hO, hJO, hOKN⟩ := _root_.mem_nhdsSetWithin.mp h.mem_nhdsSetWithin
  intro x hx
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Filter.inter_mem (hO.mem_nhds (hJO hx))
      (mem_interior_iff_mem_nhds.mp (hJK hx))) hOKN)

open Classical in
theorem exists_common_solid_torus_neighborhood
    (K S₀ S₁ : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite S₀.faces] [Finite S₁.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (horK : IsOrientable 3 K)
    (hS₀ : IsCombinatorialManifoldWithBoundary 2 S₀)
    (hS₁ : IsCombinatorialManifoldWithBoundary 2 S₁)
    (hor₀ : IsOrientable 2 S₀) (hor₁ : IsOrientable 2 S₁)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ interior K.space)
    (hS₀K : S₀.space ⊆ K.space) (hS₁K : S₁.space ⊆ K.space)
    (hJS₀ : J ⊆ S₀.space) (hJS₁ : J ⊆ S₁.space) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsTopologicalSolidTorus N.space ∧
      J ⊆ interior N.space ∧ N.space ⊆ K.space ∧ N.space ⊆ U ∧
      IsCommonAnnularDerivedNeighborhood K N.space J S₀.space S₁.space := by
  obtain ⟨A, hA, hAU⟩ := exists_common_annular_derivedNeighborhood_of_isOrientable
    K S₀ S₁ hS₀ hS₁ hor₀ hor₁ hJ (hJK.trans interior_subset) hS₀K hS₁K
    hJS₀ hJS₁ hU hJU
  obtain ⟨N, -, hNfin, hN, hNspace, hsolid, -⟩ := hA.exists_solid_torus hK horK hJ
  exact ⟨N, hNfin, hN, hNspace.symm ▸ hsolid,
    hNspace.symm ▸ hA.subset_interior hJK, hNspace.subset.trans hA.subset_ambient,
    hNspace.subset.trans hAU, hNspace.symm ▸ hA⟩

open Classical in
theorem exists_common_solid_torus_neighborhood_of_finrank_eq_three
    (S₀ S₁ : Geometry.SimplicialComplex ℝ E) [Finite S₀.faces] [Finite S₁.faces]
    (hS₀ : IsCombinatorialManifoldWithBoundary 2 S₀)
    (hS₁ : IsCombinatorialManifoldWithBoundary 2 S₁)
    (hor₀ : IsOrientable 2 S₀) (hor₁ : IsOrientable 2 S₁)
    (hdim : Module.finrank ℝ E = 3) {J U : Set E} (hJ : IsPLSphere 1 J)
    (hJS₀ : J ⊆ S₀.space) (hJS₁ : J ⊆ S₁.space) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ K N : Geometry.SimplicialComplex ℝ E,
      K.faces.Finite ∧ IsPLBall 3 K.space ∧ N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsTopologicalSolidTorus N.space ∧
      J ⊆ interior N.space ∧ N.space ⊆ U ∧
      IsCommonAnnularDerivedNeighborhood K N.space J S₀.space S₁.space := by
  obtain ⟨T, hT, hTcard, hST⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    ((isPolyhedron_space S₀).isCompact.union (isPolyhedron_space S₁).isCompact).isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hSint : S₀.space ∪ S₁.space ⊆ interior K.space := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
    exact hST
  obtain ⟨N, hNfin, hN, hsolid, hJN, -, hNU, hcommon⟩ :=
    exists_common_solid_torus_neighborhood K S₀ S₁
      hKball.isCombinatorialManifoldWithBoundary (isOrientable_of_isPLBall hKball)
      hS₀ hS₁ hor₀ hor₁ hJ (hJS₀.trans (subset_union_left.trans hSint))
      (subset_union_left.trans (hSint.trans interior_subset))
      (subset_union_right.trans (hSint.trans interior_subset)) hJS₀ hJS₁ hU hJU
  exact ⟨K, N, Set.toFinite _, hKball, hNfin, hN, hsolid, hJN, hNU, hcommon⟩

end DifferentialGeometry.Topology.PiecewiseLinear
