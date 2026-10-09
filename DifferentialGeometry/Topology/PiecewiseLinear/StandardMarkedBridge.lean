/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StandardBoxBridge
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Q" => (ℝ × ℝ) × ℝ
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "p" => stdCenter 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

private theorem exists_centered_square_parametrization :
    ∃ f : (Fin 3 → ℝ) → ℝ × ℝ, IsPLHomeomorphOn f Δ (J ×ˢ J) ∧ f p = 0 := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  have hP : IsPLBall 2 (J ×ˢ J) :=
    isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hP
  have hfront : (boundaryComplex 2 K).space = frontier (J ×ˢ J) := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) K hK.isCombinatorialManifoldWithBoundary, hKspace]
  have h0int : (0 : ℝ × ℝ) ∈ interior (J ×ˢ J) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨by norm_num, by norm_num⟩
  apply hP.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq_of_notMem_boundaryComplex K hKspace
  exact ⟨interior_subset h0int, by rw [hfront]; exact fun h => h.2 h0int⟩

theorem exists_isBridgeDisk_prism_axis :
    ∃ (C B : Set E3) (ρ : (Fin 3 → ℝ) × ℝ → E3),
      IsPLBall 3 C ∧ IsPLHomeomorphOn ρ (Δ ×ˢ I) C ∧
      IsBridgeDisk C (ρ '' ({p} ×ˢ I)) B (ρ (p, 0)) (ρ (p, 1)) := by
  classical
  obtain ⟨f, hf, hfp⟩ := exists_centered_square_parametrization
  let C₀ : Set Q := (J ×ˢ J) ×ˢ I
  let B₀ : Set Q := (I ×ˢ {(0 : ℝ)}) ×ˢ I
  let A₀ : Set Q := {((0 : ℝ), (0 : ℝ))} ×ˢ I
  have hC₀ : IsPLBall 3 C₀ := isPLBall_standardBox
  have hbridge : IsBridgeDisk C₀ A₀ B₀ (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ((0, 0), 1) :=
    isBridgeDisk_standardBox_axis
  let e : Q ≃ₗ[ℝ] E3 := LinearEquiv.ofFinrankEq Q E3 (by simp [Module.finrank_prod])
  let C := e '' C₀
  let B := e '' B₀
  have he : IsPLHomeomorphOn e C₀ C :=
    (isPLHomeomorphOn_univ_of_affineEquiv e.toAffineEquiv).restrict hC₀.isPolyhedron
      (subset_univ _)
  have hC : IsPLBall 3 C := hC₀.of_isPLHomeomorphOn he
  let ρ : (Fin 3 → ℝ) × ℝ → E3 := e ∘ Prod.map f id
  have hρ : IsPLHomeomorphOn ρ (Δ ×ˢ I) C :=
    (hf.prodMap (isPLBall_Icc zero_lt_one).isPolyhedron.isPLHomeomorphOn_id).trans he
  have haxis : ρ '' ({p} ×ˢ I) = e '' A₀ := by
    change (e ∘ Prod.map f id) '' ({p} ×ˢ I) = e '' A₀
    rw [image_comp, prodMap_image_prod, image_singleton, hfp, image_id]
    rfl
  have h0 : ρ (p, 0) = e ((0, 0), 0) := by
    change e (f p, (0 : ℝ)) = e ((0, 0), 0)
    rw [hfp]
    rfl
  have h1 : ρ (p, 1) = e ((0, 0), 1) := by
    change e (f p, (1 : ℝ)) = e ((0, 0), 1)
    rw [hfp]
    rfl
  refine ⟨C, B, ρ, hC, hρ, ?_⟩
  rw [haxis, h0, h1]
  exact hbridge.image he (by simp [Module.finrank_prod])
    hC₀.isPolyhedron.isClosed hC.isPolyhedron.isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
