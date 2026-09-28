/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HalfArcRectangle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_disk_arc_pair_of_boundary_singleton
    {D A : Set E} {D' A' : Set F}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0})
    {r' : (Fin 3 → ℝ) → F} (hr' : IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D')
    {η' : ℝ → F} (hη' : IsPLHomeomorphOn η' (Icc 0 1) A') (hAD' : A' ⊆ D')
    (hmeet' : A' ∩ (r' '' stdSimplexBoundary 2) = {η' 0}) :
    ∃ f : E → F, IsPLHomeomorphOn f D D' ∧ f '' A = A' ∧
      f (η 0) = η' 0 ∧ f (η 1) = η' 1 := by
  obtain ⟨g, hg, hg0, hg1, hgA⟩ :=
    exists_isPLHomeomorphOn_rectangle_of_boundary_singleton hr hη hAD hmeet
  obtain ⟨g', hg', hg0', hg1', hgA'⟩ :=
    exists_isPLHomeomorphOn_rectangle_of_boundary_singleton hr' hη' hAD' hmeet'
  let P := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let v := Function.invFunOn g P
  have hleft : ∀ z ∈ P, v (g z) = z := fun _ hz => hg.bijOn.invOn_invFunOn.1 hz
  have hAinv : v '' A = Icc (0 : ℝ) (1 / 2) ×ˢ {(0 : ℝ)} := by
    rw [← hgA, image_image]
    exact (show EqOn (v ∘ g) id (Icc (0 : ℝ) (1 / 2) ×ˢ {(0 : ℝ)}) from
      fun z hz => hleft z ⟨⟨hz.1.1, hz.1.2.trans (by norm_num)⟩,
        by rw [show z.2 = 0 from hz.2]; norm_num⟩).image_eq.trans (image_id _)
  refine ⟨g' ∘ v, hg.symm.trans hg', ?_, ?_, ?_⟩
  · rw [image_comp, hAinv, hgA']
  · change g' (v (η 0)) = η' 0
    rw [← hg0, hleft (0, 0) (by norm_num [P]), hg0']
  · change g' (v (η 1)) = η' 1
    rw [← hg1, hleft (1 / 2, 0) (by norm_num [P]), hg1']

end DifferentialGeometry.Topology.PiecewiseLinear
