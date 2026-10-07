/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ShiftedModel

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.Horospherical

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V₃" => Fin 3 → ℝ

theorem shiftedModel_mfderiv_injective (r₀ : ℝ) (x : V₃) :
    Function.Injective (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x) := by
  apply (injective_iff_map_eq_zero
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x)).mpr
  intro u hu
  have hm := shiftedModel_metric r₀ x u u
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

def shiftedModelTangentEquiv (r₀ : ℝ) (x : V₃) : V₃ ≃L[ℝ] E₃ := by
  let A : V₃ →L[ℝ] E₃ := mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x
  have hi : Function.Injective A := shiftedModel_mfderiv_injective r₀ x
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := V₃) (V₂ := E₃) (f := A.toLinearMap) (by simp)).mp hi
  exact ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)

theorem shiftedModelTangentEquiv_apply (r₀ : ℝ) (x u : V₃) :
    shiftedModelTangentEquiv r₀ x u =
      mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x u := rfl

theorem shiftedModel_isLocalDiffeomorph (r₀ : ℝ) :
    IsLocalDiffeomorph 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ (shiftedModel r₀) := by
  intro x
  apply
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      (shiftedModel r₀) (U := Set.univ)
      (contMDiff_shiftedModel r₀).contMDiffOn isOpen_univ x
      (Set.mem_univ x) (shiftedModelTangentEquiv r₀ x)
  change HasMFDerivAt 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x)
  exact ((contMDiff_shiftedModel r₀).mdifferentiableAt (by simp)).hasMFDerivAt

theorem shiftedModel_slice_injective (r₀ r : ℝ) :
    Function.Injective (fun z : Fin 2 → ℝ => shiftedModel r₀ ![r, z 0, z 1]) := by
  intro a b hab
  have heq :
      model ![r - r₀, Real.exp (-r₀ / 2) * a 0, Real.exp (-r₀ / 2) * a 1] =
        model ![r - r₀, Real.exp (-r₀ / 2) * b 0, Real.exp (-r₀ / 2) * b 1] := hab
  have hz : (![Real.exp (-r₀ / 2) * a 0, Real.exp (-r₀ / 2) * a 1] : Fin 2 → ℝ) =
      ![Real.exp (-r₀ / 2) * b 0, Real.exp (-r₀ / 2) * b 1] :=
    model_slice_injective (r - r₀) heq
  funext i
  have hi := congrFun hz i
  fin_cases i <;> exact mul_left_cancel₀ (Real.exp_ne_zero _) hi

end DifferentialGeometry.Geometry.Hyperbolic.Horospherical
