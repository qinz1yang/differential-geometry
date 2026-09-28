/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_isPLHomeomorphOn_ball_pair_of_disk_inter
    {C₁ C₂ : Set E3} (h₁ : IsPLBall 3 C₁) (h₂ : IsPLBall 3 C₂)
    (hD : IsPLBall 2 (C₁ ∩ C₂))
    (hD₁ : C₁ ∩ C₂ ⊆ frontier C₁) (hD₂ : C₁ ∩ C₂ ⊆ frontier C₂) :
    ∃ P Q : Set E3, IsPLBall 3 P ∧ IsPLBall 3 Q ∧
      IsPLBall 3 (P ∪ Q) ∧ IsPLBall 2 (P ∩ Q) ∧
      P ∩ Q ⊆ frontier P ∧ P ∩ Q ⊆ frontier Q ∧
      ∃ φ : E3 → E3, IsPLHomeomorphOn φ (C₁ ∪ C₂) (P ∪ Q) ∧
        φ '' C₁ = P ∧ φ '' C₂ = Q ∧ φ '' (C₁ ∩ C₂) = P ∩ Q := by
  classical
  let _ : DecidableEq E3 := Classical.decEq _
  obtain ⟨P, Q, hP, hQ, hPQ, hI, hIP, hIQ⟩ := exists_isPLBall_pair_with_disk_inter
  obtain ⟨K, hfinK, hKspace⟩ := h₁.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hfinL, hLspace⟩ := h₂.isPolyhedron.exists_simplicialComplex
  obtain ⟨M, hfinM, hMspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨N, hfinN, hNspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfinK.to_subtype
  let _ : Finite L.faces := hfinL.to_subtype
  let _ : Finite M.faces := hfinM.to_subtype
  let _ : Finite N.faces := hfinN.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ h₁
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ h₂
  have hM : IsPLBall 3 M.space := hMspace.symm ▸ hP
  have hN : IsPLBall 3 N.space := hNspace.symm ▸ hQ
  have hDK : K.space ∩ L.space ⊆ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary,
      hKspace, hLspace]
    exact hD₁
  have hDL : K.space ∩ L.space ⊆ (boundaryComplex 3 L).space := by
    rw [← frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary,
      hKspace, hLspace]
    exact hD₂
  have hIM : P ∩ Q ⊆ (boundaryComplex 3 M).space := by
    rw [← frontier_space_eq_boundaryComplex_space hM.isCombinatorialManifoldWithBoundary,
      hMspace]
    exact hIP
  have hIN : P ∩ Q ⊆ (boundaryComplex 3 N).space := by
    rw [← frontier_space_eq_boundaryComplex_space hN.isCombinatorialManifoldWithBoundary,
      hNspace]
    exact hIQ
  obtain ⟨u, hu⟩ := hD
  obtain ⟨v, hv⟩ := hI
  have hu' : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (K.space ∩ L.space) := by
    rw [hKspace, hLspace]
    exact hu
  have hv' : IsPLHomeomorphOn v (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (M.space ∩ N.space) := by
    rw [hMspace, hNspace]
    exact hv
  have hIM' : M.space ∩ N.space ⊆ (boundaryComplex 3 M).space := by
    rwa [hMspace, hNspace]
  have hIN' : M.space ∩ N.space ⊆ (boundaryComplex 3 N).space := by
    rwa [hMspace, hNspace]
  have hg : IsPLHomeomorphOn
      (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)))
      (K.space ∩ L.space) (M.space ∩ N.space) := hu'.symm.trans hv'
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex K M hK hM
      ⟨u, hu'⟩ hDK hg hIM'
  obtain ⟨f₂, hf₂, hf₂g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex L N hL hN
      ⟨u, hu'⟩ hDL hg hIN'
  have hfg : EqOn f₁ f₂ (K.space ∩ L.space) := hf₁g.trans hf₂g.symm
  have hmeet : f₁ '' (K.space ∩ L.space) = M.space ∩ N.space := by
    exact hf₁g.image_eq.trans hg.image_eq
  let φ := K.space.piecewise f₁ f₂
  have hφ : IsPLHomeomorphOn φ (K.space ∪ L.space) (M.space ∪ N.space) :=
    hf₁.piecewise hf₂ hK.isPolyhedron hL.isPolyhedron hfg hmeet
  have hφ₁ : EqOn φ f₁ K.space := K.space.piecewise_eqOn f₁ f₂
  have hφ₂ : EqOn φ f₂ L.space := by
    intro x hx
    by_cases hxK : x ∈ K.space
    · change K.space.piecewise f₁ f₂ x = f₂ x
      rw [K.space.piecewise_eq_of_mem f₁ f₂ hxK]
      exact hfg ⟨hxK, hx⟩
    · change K.space.piecewise f₁ f₂ x = f₂ x
      exact K.space.piecewise_eq_of_notMem f₁ f₂ hxK
  refine ⟨P, Q, hP, hQ, hPQ, ⟨v, hv⟩, hIP, hIQ, φ, ?_, ?_, ?_, ?_⟩
  · rwa [hKspace, hLspace, hMspace, hNspace] at hφ
  · rw [← hKspace, ← hMspace, hφ₁.image_eq]
    exact hf₁.image_eq
  · rw [← hLspace, ← hNspace, hφ₂.image_eq]
    exact hf₂.image_eq
  · rw [← hKspace, ← hLspace, hφ₁.mono inter_subset_left |>.image_eq]
    rw [hmeet, hMspace, hNspace]

end DifferentialGeometry.Topology.PiecewiseLinear
