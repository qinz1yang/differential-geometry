/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCenteredPrism
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_centered_prism_of_ball_pair_inter_disk
    {C₁ C₂ D : Set E3} (h₁ : IsPLBall 3 C₁) (h₂ : IsPLBall 3 C₂)
    {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : C₁ ∩ C₂ = D)
    (hD₁ : D ⊆ frontier C₁) (hD₂ : D ⊆ frontier C₂) :
    ∃ ρ : (Fin 3 → ℝ) × ℝ → E3,
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) (C₁ ∪ C₂) ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ρ (x, 0) = r x) ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) = C₁ ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) = C₂ := by
  classical
  let _ : DecidableEq E3 := Classical.decEq _
  obtain ⟨K, hKfin, hKspace⟩ := h₁.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := h₂.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ h₁
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ h₂
  have hDK : D ⊆ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary,
      hKspace]
    exact hD₁
  have hDL : D ⊆ (boundaryComplex 3 L).space := by
    rw [← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary,
      hLspace]
    exact hD₂
  have hI : K.space ∩ L.space = D := by rw [hKspace, hLspace]; exact hmeet
  obtain ⟨ρ, hρ, hρzero, hρ₁, hρ₂⟩ :=
    exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair
      (isPLBall_stdSimplex 2) K L hK hL hDK hDL hI hr
  refine ⟨ρ, ?_, hρzero, ?_, ?_⟩
  · rwa [hKspace, hLspace] at hρ
  · rwa [hKspace] at hρ₁
  · rwa [hLspace] at hρ₂

end DifferentialGeometry.Topology.PiecewiseLinear
