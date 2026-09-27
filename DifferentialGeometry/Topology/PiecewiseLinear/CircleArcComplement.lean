/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.isPLBall_closure_sdiff_one {S A : Set E}
    (hS : IsPLSphere 1 S) (hA : IsPLBall 1 A) (hAS : A ⊆ S) :
    IsPLBall 1 (closure (S \ A)) := by
  obtain ⟨C, f, hC, hf⟩ := exists_planar_isPLHomeomorphOn_of_isPLSphere_one hS
  let B := f '' A
  have hB : IsPLBall 1 B := hA.of_isPLHomeomorphOn (hf.restrict hA.isPolyhedron hAS)
  have hBC : B ⊆ C := (image_mono hAS).trans hf.image_eq.subset
  obtain ⟨p, q, hBpq⟩ := hB.isArc.exists_isArcBetween
  obtain ⟨D, hcut, -, hD⟩ := exists_isCutPair_of_isArcBetween_subset_isPLSphere hC hBpq hBC
  have hdiff : C \ B = D \ {p, q} := by
    rw [← hcut.union_eq]
    ext x
    have hx : x ∈ B ∩ D ↔ x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [hcut.inter_eq]
    simp only [mem_sdiff, mem_union, mem_inter_iff] at hx ⊢
    tauto
  have hclosure : closure (C \ B) = D := by
    obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hD hcut.snd
    rw [hdiff, ← hδ0, ← hδ1]
    exact hδ.closure_sdiff_endpoints zero_lt_one
  have himage : f '' closure (S \ A) = D := by
    rw [hf.image_closure hS.isPolyhedron.isCompact sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hAS, hf.image_eq]
    exact hclosure
  let g := Function.invFunOn f S
  have hback : g '' D = closure (S \ A) := by
    rw [← himage, image_image]
    have hfix : EqOn (g ∘ f) id (closure (S \ A)) := fun x hx =>
      hf.bijOn.invOn_invFunOn.1 (closure_minimal sdiff_subset hS.isPolyhedron.isClosed hx)
    exact hfix.image_eq.trans (image_id _)
  have hball := hD.of_isPLHomeomorphOn (hf.symm.restrict hD.isPolyhedron hcut.snd_subset)
  exact hback ▸ hball

end DifferentialGeometry.Topology.PiecewiseLinear
