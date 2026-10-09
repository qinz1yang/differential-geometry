/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.BoundaryOrientationContraction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Module
namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

def orientationByParity {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : ZMod 2) (o : Orientation ℝ V (Fin n)) : Orientation ℝ V (Fin n) :=
  if s = 0 then o else -o

theorem orientationByParity_add {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (s t : ZMod 2) (o : Orientation ℝ V (Fin n)) :
    orientationByParity (s + t) o =
      orientationByParity s (orientationByParity t o) := by
  have h₁ : (1 : ZMod 2) ≠ 0 := by decide
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz s with rfl | rfl
  · rcases hz t with rfl | rfl
    · simp [orientationByParity]
    · simp [orientationByParity, h₁]
  · rcases hz t with rfl | rfl
    · simp [orientationByParity, h₁]
    · simp [orientationByParity, h₁, h₂]

theorem normalFirstOrientation_parity
    (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) (s : ZMod 2) :
    normalFirstOrientation e b (orientationByParity s o) =
      orientationByParity s (normalFirstOrientation e b o) := by
  have h₁ : (1 : ZMod 2) ≠ 0 := by decide
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz s with rfl | rfl
  · simp [orientationByParity]
  · simp [orientationByParity, h₁, normalFirstOrientation_neg]

theorem normalFirstOrientation_opposite_normal_parity
    (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) (s₁ s₂ : ZMod 2) :
    normalFirstOrientation (normalFirstReflection.trans e) b
        (orientationByParity s₂ o) =
      orientationByParity (s₁ + s₂ + 1)
        (normalFirstOrientation e b (orientationByParity s₁ o)) := by
  have h₁ : (1 : ZMod 2) ≠ 0 := by decide
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz s₁ with rfl | rfl
  · rcases hz s₂ with rfl | rfl
    · simp [orientationByParity, h₁, normalFirstOrientation_reflect_normal]
    · simp [orientationByParity, h₁, h₂, normalFirstOrientation_reflect_normal,
        normalFirstOrientation_neg]
  · rcases hz s₂ with rfl | rfl
    · simp [orientationByParity, h₁, h₂, normalFirstOrientation_reflect_normal,
        normalFirstOrientation_neg]
    · simp [orientationByParity, h₁, h₂, normalFirstOrientation_reflect_normal,
        normalFirstOrientation_neg]

end DifferentialGeometry.Topology.Manifold
