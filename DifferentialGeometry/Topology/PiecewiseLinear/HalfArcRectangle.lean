/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HalfArcCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.RectangleCrosscutCoordinates

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_rectangle_of_boundary_singleton
    {D A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0}) :
    ∃ g : ℝ × ℝ → E,
      IsPLHomeomorphOn g (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) D ∧
      g (0, 0) = η 0 ∧ g (1 / 2, 0) = η 1 ∧
      g '' (Icc (0 : ℝ) (1 / 2) ×ˢ {(0 : ℝ)}) = A := by
  classical
  obtain ⟨P, ρ, hP, hρ, hρbd⟩ := hr.exists_planarModel
  let σ := Function.invFunOn ρ P
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hη
  let A' := σ '' A
  have hη' : IsPLHomeomorphOn (σ ∘ η) (Icc 0 1) A' :=
    hη.trans (hρ.symm.restrict hA.isPolyhedron hAD)
  have hA'P : A' ⊆ P := (image_mono hAD).trans hρ.symm.image_eq.subset
  have hbdD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hσbd : σ '' (r '' stdSimplexBoundary 2) = frontier P := by
    rw [← hρbd, image_image]
    exact (show EqOn (σ ∘ ρ) id (frontier P) from fun x hx =>
      hρ.bijOn.invOn_invFunOn.1 (hP.isPolyhedron.isClosed.frontier_subset hx)).image_eq.trans
        (image_id _)
  have hmeet' : A' ∩ frontier P = {(σ ∘ η) 0} := by
    rw [← hσbd, ← hρ.symm.bijOn.injOn.image_inter hAD hbdD, hmeet, image_singleton]
    rfl
  obtain ⟨Q, R, γ, hγ, -, hQP, -, hγ0, hγmid, hγA, hγbd⟩ :=
    hη'.exists_crosscut_extension_of_boundary_singleton hP hA'P hmeet'
  obtain ⟨p, hp⟩ := hP
  have hγbd' : Q ∩ (p '' stdSimplexBoundary 2) = {γ 0, γ 1} := by
    rw [hp.image_stdSimplexBoundary]
    exact hγbd
  obtain ⟨f, hf, hfγ⟩ :=
    exists_isPLHomeomorphOn_rectangle_eq_on_crosscut hp hγ hQP hγbd'
  have hη0 : η 0 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have hη1 : η 1 ∈ A := hη.bijOn.mapsTo (by norm_num)
  have hinv : ∀ x ∈ A, ρ (σ x) = x := fun x hx => hρ.bijOn.invOn_invFunOn.2 (hAD hx)
  have hback : ρ '' A' = A := by
    rw [show A' = σ '' A from rfl, image_image]
    exact (show EqOn (ρ ∘ σ) id A from hinv).image_eq.trans (image_id _)
  have hfA : f '' (Icc (0 : ℝ) (1 / 2) ×ˢ {(0 : ℝ)}) = A' := by
    have heq : EqOn f (γ ∘ Prod.fst) (Icc (0 : ℝ) (1 / 2) ×ˢ {(0 : ℝ)}) := by
      rintro ⟨x, t⟩ ⟨hx, rfl⟩
      exact hfγ x ⟨hx.1, hx.2.trans (by norm_num)⟩
    rw [heq.image_eq, image_comp, fst_image_prod _ (singleton_nonempty _), hγA]
  refine ⟨ρ ∘ f, hf.trans hρ, ?_, ?_, ?_⟩
  · change ρ (f (0, 0)) = η 0
    rw [hfγ 0 (by norm_num), hγ0]
    exact hinv _ hη0
  · change ρ (f (1 / 2, 0)) = η 1
    rw [hfγ (1 / 2) (by norm_num), hγmid]
    exact hinv _ hη1
  · rw [image_comp, hfA, hback]

end DifferentialGeometry.Topology.PiecewiseLinear
