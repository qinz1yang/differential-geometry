/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeArcShrinking

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isBridgeDisk_closure_boundary_sdiff_of_boundary_arc
    {C D β : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDC : D ⊆ C)
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β)
    (hβ : β ⊆ r '' stdSimplexBoundary 2) (htrace : D ∩ frontier C = β) :
    IsBridgeDisk C (closure ((r '' stdSimplexBoundary 2) \ β)) D (γ 0) (γ 1) := by
  obtain ⟨U, η, hη, hη0, hη1, hcover, hmeet⟩ :=
    exists_complementary_arc_of_isPLSphere_one hr.isPLSphere_image_stdSimplexBoundary hγ hβ
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hbd : r '' stdSimplexBoundary 2 = (boundaryComplex 2 K).space :=
    hr.image_stdSimplexBoundary_eq_boundaryComplex K hKD
  have hUK : U ⊆ (boundaryComplex 2 K).space :=
    subset_union_right.trans (hcover.trans hbd).subset
  have hUD : U ⊆ D :=
    hUK.trans ((boundaryComplex_space_subset 2 K).trans hKD.subset)
  have hUfront : U ∩ frontier C = {η 0, η 1} := by
    rw [hη0, hη1, ← hmeet, inter_comm β U]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, htrace.subset ⟨hUD hx.1, hx.2⟩⟩
    · exact fun hx => ⟨hx.1, (htrace.symm.subset hx.2).2⟩
  have hbridge : IsBridgeDisk C U D (γ 0) (γ 1) := by
    rw [← hKD, ← hη0, ← hη1]
    apply exists_isBridgeDisk_of_boundary_cover K (hKD.symm ▸ hD)
      (hKD.subset.trans hDC) hη hUK
    · rw [hKD, htrace]
      exact hβ.trans hbd.subset
    · rw [← hbd, ← hcover]
      rintro x (hxβ | hxU)
      · exact Or.inr (htrace.symm.subset hxβ).2
      · exact Or.inl hxU
    · exact hUfront
  have heq := hbridge.closure_boundary_sdiff_inter_frontier K hKD
  rw [← hbd, htrace] at heq
  exact heq.symm ▸ hbridge

end DifferentialGeometry.Topology.PiecewiseLinear
