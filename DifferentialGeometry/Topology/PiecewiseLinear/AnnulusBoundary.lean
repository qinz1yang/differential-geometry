/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurvePrism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLHomeomorphOn.exists_annulus_complex {J : Set E} (hJ : IsPLSphere 1 J)
    {a b : ℝ} (hab : a < b) {W : Set F} {ρ : E × ℝ → F}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) W) :
    ∃ A : Geometry.SimplicialComplex ℝ F, A.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsConnected A.space ∧ A.space = W ∧
      (boundaryComplex 2 A).space = ρ '' (J ×ˢ {a, b}) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨L, hLfin, hLspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsCombinatorialManifold 1 L := (hLspace.symm ▸ hJ).isCombinatorialManifold
  have hLbd : (boundaryComplex 1 L).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hL.boundaryComplex_faces_eq_empty L]
    simp
  obtain ⟨P, hPfin, hPspace⟩ :=
    (hJ.isPolyhedron.prod (isPLBall_Icc hab).isPolyhedron).exists_simplicialComplex
  let _ : Finite P.faces := hPfin.to_subtype
  have hLP : P.space = L.space ×ˢ Icc a b := by rw [hLspace, hPspace]
  have hP := hL.isCombinatorialManifoldWithBoundary.prod_Icc_one L hab P hLP
  have hPbd : (boundaryComplex 2 P).space = J ×ˢ {a, b} := by
    rw [boundaryComplex_space_prod_Icc_one L hL.isCombinatorialManifoldWithBoundary hab P hLP,
      hLbd, empty_prod, union_empty, hLspace]
  have hW : IsPolyhedron W := hρ.image_eq ▸
    (hJ.isPolyhedron.prod (isPLBall_Icc hab).isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨A, hAfin, hAspace⟩ := hW.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hmap : IsPLHomeomorphOn ρ P.space A.space := by
    rw [hPspace, hAspace]
    exact hρ
  have hAc : IsConnected A.space := by
    rw [hAspace, ← hρ.image_eq]
    exact (hJ.isConnected.prod
      ((convex_Icc a b).isConnected ⟨a, le_rfl, hab.le⟩)).image
        _ hρ.isPiecewiseAffineOn.continuousOn
  refine ⟨A, hAfin, hP.of_isPLHomeomorphOn hmap, hAc, hAspace, ?_⟩
  rw [boundaryComplex_space_of_isPLHomeomorphOn P A hP hmap, hPbd]

end DifferentialGeometry.Topology.PiecewiseLinear
