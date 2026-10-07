/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ManifoldMetric
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.Horospherical

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V₃" => Fin 3 → ℝ

theorem model_mfderiv_injective (x : V₃) :
    Function.Injective (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x) := by
  apply (injective_iff_map_eq_zero
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x)).mpr
  intro u hu
  have hm := model_metric x u u
  rw [hu] at hm
  simp only [map_zero] at hm
  have he : 0 < Real.exp (-x 0) := Real.exp_pos _
  have hnonneg : 0 ≤ Real.exp (-x 0) * ((u 1)^2 + (u 2)^2) :=
    mul_nonneg he.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have h₀ : (u 0)^2 = 0 := by nlinarith [sq_nonneg (u 0)]
  have hweighted : Real.exp (-x 0) * ((u 1)^2 + (u 2)^2) = 0 := by
    nlinarith
  have hsum : (u 1)^2 + (u 2)^2 = 0 :=
    (mul_eq_zero.mp hweighted).resolve_left (Real.exp_ne_zero _)
  have h₁ : u 1 = 0 := by nlinarith [sq_nonneg (u 2)]
  have h₂ : u 2 = 0 := by nlinarith [sq_nonneg (u 1)]
  funext i
  fin_cases i
  · exact sq_eq_zero_iff.mp h₀
  · exact h₁
  · exact h₂

theorem model_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ model := by
  intro x
  let A : V₃ →L[ℝ] E₃ := mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x
  have hi : Function.Injective A := model_mfderiv_injective x
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := V₃) (V₂ := E₃) (f := A.toLinearMap) (by simp)).mp hi
  let L : V₃ ≃L[ℝ] E₃ := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  apply
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      model (U := Set.univ) contMDiff_model.contMDiffOn isOpen_univ x
      (Set.mem_univ x) L
  change HasMFDerivAt 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x)
  exact (contMDiff_model.mdifferentiableAt (by simp)).hasMFDerivAt

end DifferentialGeometry.Geometry.Hyperbolic.Horospherical
