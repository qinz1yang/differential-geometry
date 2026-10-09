/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBallPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_union_of_boundary_disk
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 3 K.space) (hL : IsPLBall 3 L.space) (hD : IsPLBall 2 (K.space ∩ L.space))
    (hDK : K.space ∩ L.space ⊆ (boundaryComplex 3 K).space)
    (hDL : K.space ∩ L.space ⊆ (boundaryComplex 3 L).space) :
    IsPLBall 3 (K.space ∪ L.space) := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨P, Q, hP, hQ, hPQ, hI, hIP, hIQ⟩ := exists_isPLBall_pair_with_disk_inter
  obtain ⟨M, hfinM, hMspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨N, hfinN, hNspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite M.faces := hfinM.to_subtype
  let _ : Finite N.faces := hfinN.to_subtype
  have hM : IsPLBall 3 M.space := hMspace.symm ▸ hP
  have hN : IsPLBall 3 N.space := hNspace.symm ▸ hQ
  have hIM : P ∩ Q ⊆ (boundaryComplex 3 M).space := by
    rw [← frontier_space_eq_boundaryComplex_space hM.isCombinatorialManifoldWithBoundary, hMspace]
    exact hIP
  have hIN : P ∩ Q ⊆ (boundaryComplex 3 N).space := by
    rw [← frontier_space_eq_boundaryComplex_space hN.isCombinatorialManifoldWithBoundary, hNspace]
    exact hIQ
  obtain ⟨u, hu⟩ := hD
  have hD : IsPLBall 2 (K.space ∩ L.space) := ⟨u, hu⟩
  obtain ⟨v, hv⟩ := hI
  have hg := hu.symm.trans hv
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex K M hK hM hD hDK hg hIM
  obtain ⟨f₂, hf₂, hf₂g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex L N hL hN hD hDL hg hIN
  have hfg : EqOn f₁ f₂ (K.space ∩ L.space) := hf₁g.trans hf₂g.symm
  have hmeet : f₁ '' (K.space ∩ L.space) = M.space ∩ N.space := by
    rw [hMspace, hNspace]
    exact hf₁g.image_eq.trans hg.image_eq
  have h := hf₁.piecewise hf₂ hK.isPolyhedron hL.isPolyhedron hfg hmeet
  have hMN : IsPLBall 3 (M.space ∪ N.space) := by rw [hMspace, hNspace]; exact hPQ
  exact hMN.of_isPLHomeomorphOn h.symm

theorem isPLBall_union_of_inter_isPLBall_two
    {C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3))} (h₁ : IsPLBall 3 C₁) (h₂ : IsPLBall 3 C₂)
    (hD : IsPLBall 2 (C₁ ∩ C₂)) (hD₁ : C₁ ∩ C₂ ⊆ frontier C₁)
    (hD₂ : C₁ ∩ C₂ ⊆ frontier C₂) : IsPLBall 3 (C₁ ∪ C₂) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K, hfinK, hKspace⟩ := h₁.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hfinL, hLspace⟩ := h₂.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfinK.to_subtype
  let _ : Finite L.faces := hfinL.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ h₁
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ h₂
  rw [← hKspace, ← hLspace] at hD hD₁ hD₂ ⊢
  rw [frontier_space_eq_boundaryComplex_space hK.isCombinatorialManifoldWithBoundary] at hD₁
  rw [frontier_space_eq_boundaryComplex_space hL.isCombinatorialManifoldWithBoundary] at hD₂
  exact isPLBall_union_of_boundary_disk K L hK hL hD hD₁ hD₂

end DifferentialGeometry.Topology.PiecewiseLinear
