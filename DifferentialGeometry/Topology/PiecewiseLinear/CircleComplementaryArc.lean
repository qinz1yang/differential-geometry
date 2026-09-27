/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_complementary_arc_of_isPLSphere_one {S A : Set E}
    (hS : IsPLSphere 1 S) {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAS : A ⊆ S) :
    ∃ (B : Set E) (δ : ℝ → E), IsPLHomeomorphOn δ (Icc 0 1) B ∧
      δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ A ∪ B = S ∧ A ∩ B = {γ 0, γ 1} := by
  obtain ⟨C, f, hC, hf⟩ := exists_planar_isPLHomeomorphOn_of_isPLSphere_one hS
  have hA : IsPLBall 1 A := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hγf := hγ.trans (hf.restrict hA.isPolyhedron hAS)
  have harc : Schoenflies.IsArcBetween (f '' A) (f (γ 0)) (f (γ 1)) :=
    ⟨f ∘ γ, hγf.isPiecewiseAffineOn.continuousOn, hγf.bijOn.injOn, hγf.image_eq, rfl, rfl⟩
  have hAC : f '' A ⊆ C := (image_mono hAS).trans hf.image_eq.subset
  obtain ⟨R, hcut, -, hR⟩ := exists_isCutPair_of_isArcBetween_subset_isPLSphere hC harc hAC
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hR hcut.snd
  let g := Function.invFunOn f S
  have hback : g '' (f '' A) = A := by
    rw [image_image]
    exact (show EqOn (g ∘ f) id A from fun x hx =>
      hf.bijOn.invOn_invFunOn.1 (hAS hx)).image_eq.trans (image_id _)
  have h0 : g (f (γ 0)) = γ 0 := hf.bijOn.invOn_invFunOn.1
    (hAS (hγ.bijOn.mapsTo (by norm_num)))
  have h1 : g (f (γ 1)) = γ 1 := hf.bijOn.invOn_invFunOn.1
    (hAS (hγ.bijOn.mapsTo (by norm_num)))
  have hδg := hδ.trans (hf.symm.restrict hR.isPolyhedron hcut.snd_subset)
  refine ⟨g '' R, g ∘ δ, hδg, ?_, ?_, ?_, ?_⟩
  · change g (δ 0) = γ 0
    rw [hδ0, h0]
  · change g (δ 1) = γ 1
    rw [hδ1, h1]
  · rw [← hback, ← image_union, hcut.union_eq]
    exact hf.symm.image_eq
  · rw [← hback, ← hf.symm.bijOn.injOn.image_inter hAC hcut.snd_subset,
      hcut.inter_eq, image_pair]
    change {g (f (γ 0)), g (f (γ 1))} = {γ 0, γ 1}
    rw [h0, h1]

end DifferentialGeometry.Topology.PiecewiseLinear
