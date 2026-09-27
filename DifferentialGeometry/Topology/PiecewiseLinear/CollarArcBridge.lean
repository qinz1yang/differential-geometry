/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskBoundaryArc
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_isBridgeDisk_of_collar_arc
    {C β R : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β)
    {c : E × ℝ → E} (hc : IsPLHomeomorphOn c (β ×ˢ Icc (0 : ℝ) 1) R)
    (hRC : R ⊆ C) (hc0 : ∀ x ∈ β, c (x, 0) = x) (htrace : R ∩ frontier C = β) :
    ∃ U : Set E, IsBridgeDisk C U R (γ 0) (γ 1) := by
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hQ : IsPLBall 2 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isPLBall_two_prod hI hI
  obtain ⟨p, hp⟩ := hQ
  let f : ℝ × ℝ → E := c ∘ Prod.map γ id
  have hf : IsPLHomeomorphOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R :=
    (hγ.prodMap hI.isPolyhedron.isPLHomeomorphOn_id).trans hc
  have hpbd : p '' stdSimplexBoundary 2 =
      frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    classical
    have hQ : IsPLBall 2 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := ⟨p, hp⟩
    obtain ⟨K, hKfin, hKQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfin.to_subtype
    have hK : IsPLBall 2 K.space := hKQ.symm ▸ hQ
    rw [hp.image_stdSimplexBoundary_eq_boundaryComplex K hKQ,
      ← frontier_space_eq_boundaryComplex_space_of_finrank
        (by simp [Module.finrank_prod]) K hK.isCombinatorialManifoldWithBoundary, hKQ]
  have hside : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆
      frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
    exact fun z hz => Or.inl ⟨hz.1, Or.inl hz.2⟩
  have hβbd : β ⊆ (f ∘ p) '' stdSimplexBoundary 2 := by
    rw [image_comp, hpbd]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hx
    exact ⟨(t, 0), hside ⟨ht, rfl⟩, hc0 (γ t) (hγ.bijOn.mapsTo ht)⟩
  exact ⟨_, isBridgeDisk_closure_boundary_sdiff_of_boundary_arc
    (hp.trans hf) hRC hγ hβbd htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
