/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallReplacement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_disk_subset_with_complement
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ (C : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc 0 1) C ∧ C ⊆ K.space ∧ C ⊆ U ∧
      C ∩ (boundaryComplex 3 K).space = D ∧ (∀ x ∈ D, ρ (x, 0) = x) ∧
      MapsTo ρ (D ×ˢ Ioc 0 1) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ C) := by
  obtain ⟨C, ρ, hρ, hCK, hCU, hmeet, hfix, hpos⟩ :=
    hK.exists_collar_of_boundary_disk_subset hD hDK hU
  have hC : IsPLBall 3 C :=
    (isPLBall_three_prod hD (isPLBall_Icc (by norm_num : (0 : ℝ) < 1))).of_isPLHomeomorphOn hρ
  obtain ⟨R, hRfin, hR, hspace⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hC hCK (hmeet.symm ▸ hD)
  exact ⟨C, ρ, R, hρ, hCK, hCU, hmeet, hfix, hpos, hRfin, hR, hspace⟩

namespace IsCombinatorialManifoldWithBoundary

open Classical in
theorem
    exists_collar_of_boundary_disk_subset_with_boundary_complement
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ (C : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E) (H : E → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc 0 1) C ∧ C ⊆ K.space ∧ C ⊆ U ∧
      C ∩ (boundaryComplex 3 K).space = D ∧ (∀ x ∈ D, ρ (x, 0) = x) ∧
      MapsTo ρ (D ×ˢ Ioc 0 1) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ C) ∧
      IsPLHomeomorphOn H (boundaryComplex 3 K).space (boundaryComplex 3 R).space ∧
      EqOn H id (closure ((boundaryComplex 3 K).space \ D)) := by
  classical
  obtain ⟨C, ρ, R, hρ, hCK, hCU, hmeet, hfix, hpos, hRfin, hR, hRspace⟩ :=
    hK.exists_collar_of_boundary_disk_subset_with_complement hD hDK hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hC : IsPLBall 3 C :=
    (isPLBall_three_prod hD (isPLBall_Icc (by norm_num : (0 : ℝ) < 1))).of_isPLHomeomorphOn hρ
  obtain ⟨A, hAfin, hAC⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  obtain ⟨H, hH, hHfix⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_boundary_complement
      K A R hK (hAC.symm ▸ hC) (hAC.symm ▸ hCK)
      (by rw [hAC, hmeet]; exact hD) hR (by rw [hAC]; exact hRspace)
  have hdiff : (boundaryComplex 3 K).space \ A.space = (boundaryComplex 3 K).space \ D := by
    rw [hAC, ← hmeet]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff] at hHfix
  exact ⟨C, ρ, R, H, hρ, hCK, hCU, hmeet, hfix, hpos, hRfin, hR, hRspace, hH, hHfix⟩
end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
