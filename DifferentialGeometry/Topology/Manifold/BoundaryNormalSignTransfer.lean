/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.BoundaryNormalParity
import DifferentialGeometry.Topology.Manifold.BoundaryOrientationFrameChange

open Module

namespace DifferentialGeometry.Topology.Manifold

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

theorem normalFirstOrientation_opposite_normal_of_positive_scale
    (e₁ e₂ : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (c : ℝ) (hc : 0 < c) (w : F)
    (hn : e₂ (1, 0) = c • (-e₁ (1, 0)) + e₁ (0, w))
    (ht : ∀ v : F, e₂ (0, v) = e₁ (0, v))
    (o : Orientation ℝ E (Fin 3)) (s₁ s₂ : ZMod 2) :
    normalFirstOrientation e₂ b (orientationByParity s₂ o) =
      orientationByParity (s₁ + s₂ + 1)
        (normalFirstOrientation e₁ b (orientationByParity s₁ o)) := by
  have hnr : e₂ (1, 0) =
      c • (normalFirstReflection.trans e₁) (1, 0) +
        (normalFirstReflection.trans e₁) (0, w) := by
    have hrn : (normalFirstReflection.trans e₁) (1, (0 : F)) =
        -e₁ (1, 0) := by
      change e₁ (-1, (0 : F)) = -e₁ (1, 0)
      simpa only [Prod.neg_mk, neg_zero] using map_neg e₁ (1, (0 : F))
    have hrt : (normalFirstReflection.trans e₁) (0, w) = e₁ (0, w) := by
      simp [normalFirstReflection]
    rw [hrn, hrt]
    exact hn
  have htr : ∀ v : F, e₂ (0, v) =
      (normalFirstReflection.trans e₁) (0, v) := by
    intro v
    simpa only [normalFirstReflection, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.neg_apply, neg_zero,
      LinearEquiv.refl_apply] using ht v
  rw [normalFirstOrientation_change_positive_normal
    (normalFirstReflection.trans e₁) e₂ b c hc w hnr htr]
  exact normalFirstOrientation_opposite_normal_parity e₁ b o s₁ s₂

theorem normalFirstOrientation_opposite_normal_of_positive_scale_map
    (e₁ e₂ : (ℝ × F) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G)
    (b : Basis (Fin 2) ℝ F) (c : ℝ) (hc : 0 < c) (w : F)
    (hn : e₂ (1, 0) = c • (-e₁ (1, 0)) + e₁ (0, w))
    (ht : ∀ v : F, e₂ (0, v) = e₁ (0, v))
    (o : Orientation ℝ E (Fin 3)) (s₁ s₂ : ZMod 2) :
    normalFirstOrientation (e₂.trans g) b
        (Orientation.map (Fin 3) g (orientationByParity s₂ o)) =
      orientationByParity (s₁ + s₂ + 1)
        (normalFirstOrientation (e₁.trans g) b
          (Orientation.map (Fin 3) g (orientationByParity s₁ o))) := by
  rw [normalFirstOrientation_map, normalFirstOrientation_map]
  exact normalFirstOrientation_opposite_normal_of_positive_scale
    e₁ e₂ b c hc w hn ht o s₁ s₂

end DifferentialGeometry.Topology.Manifold
