/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DiskDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_disk_in_boundary_ball
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsPLBall 3 A.space) (hAK : A.space ⊆ K.space)
    {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDA : D ⊆ A.space)
    (hDK : D ⊆ (boundaryComplex 3 K).space) :
    ∃ (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ Q ⊆ K.space ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      Q ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 := by
  classical
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨L, hfin, hL, hLK, hLB, hDL⟩ :=
    exists_isPLBall_inter_boundaryComplex_eq_of_subset K A hK hA hAK hD hDA hDK
  let _ : Finite L.faces := hfin.to_subtype
  let S := (boundaryComplex 3 L).space
  have hS : IsPLSphere 2 S := isPLSphere_boundaryComplex_space_of_isPLBall L hL
  let Q := closure (S \ D)
  have hQL : Q ⊆ L.space := (closure_minimal sdiff_subset hS.isPolyhedron.isClosed).trans
    (boundaryComplex_space_subset 3 L)
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff hD hDL
  have hQD : Q ∩ D = r '' stdSimplexBoundary 2 := by
    rw [inter_comm]
    exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDL
  refine ⟨Q, q, hq, hQL.trans hLK, ?_, ?_⟩
  · exact (hS.image_stdSimplexBoundary_complement hD hDL hq).trans hQD
  · rw [← hQD, ← hLB, ← inter_assoc, inter_eq_left.mpr hQL]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_inter_boundaryComplex_eq
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ IsPLBall 3 L.space ∧
      L.space ⊆ K.space ∧ L.space ∩ (boundaryComplex 3 K).space = D ∧
      D ⊆ (boundaryComplex 3 L).space := by
  classical
  obtain ⟨C, hC, hCK, hDC⟩ := hK.exists_isPLBall_containing_boundary_disk hD hDK
  obtain ⟨A, hAfin, hAC⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  exact exists_isPLBall_inter_boundaryComplex_eq_of_subset K A hK (hAC.symm ▸ hC)
    (hAC.symm ▸ hCK) hD (hAC.symm ▸ hDC) hDK

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_push_boundary_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDK : D ⊆ (boundaryComplex 3 K).space) :
    ∃ (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ Q ⊆ K.space ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      Q ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 := by
  classical
  obtain ⟨C, hC, hCK, hDC⟩ := hK.exists_isPLBall_containing_boundary_disk ⟨r, hr⟩ hDK
  obtain ⟨A, hAfin, hAC⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  exact exists_isPLHomeomorphOn_disk_in_boundary_ball K A hK (hAC.symm ▸ hC)
    (hAC.symm ▸ hCK) hr (hAC.symm ▸ hDC) hDK
end DifferentialGeometry.Topology.PiecewiseLinear
