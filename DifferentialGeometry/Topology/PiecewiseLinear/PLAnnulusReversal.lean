/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.symm {C J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds C J₀ J₁) : IsPLAnnulusWithEnds C J₁ J₀ := by
  have hflip : IsPLHomeomorphOn (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
    · intro t _ u _ heq
      linarith
    · intro t ht
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      ring
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  refine ⟨J, ρ ∘ Prod.map id (fun t : ℝ => 1 - t), hJ,
    (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hflip).trans hρ, ?_, ?_⟩
  · rw [image_comp, prodMap_image_prod, image_id, image_singleton, sub_zero, ← h₁]
  · rw [image_comp, prodMap_image_prod, image_id, image_singleton, sub_self, ← h₀]

end DifferentialGeometry.Topology.PiecewiseLinear
