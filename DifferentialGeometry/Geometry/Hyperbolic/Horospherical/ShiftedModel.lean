/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ModelLocalDiffeomorph

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.Horospherical

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V₃" => Fin 3 → ℝ

private theorem model_space (x : V₃) :
    (model x).space = WithLp.toLp 2
      ![(-1 / 2) * Real.exp (-x 0 / 2) + (1 / 2) * (Real.exp (-x 0 / 2))⁻¹ +
          (1 / 8) * Real.exp (-x 0 / 2) * ((x 1)^2 + (x 2)^2),
        (1 / 2) * Real.exp (-x 0 / 2) * x 1,
        (1 / 2) * Real.exp (-x 0 / 2) * x 2] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

theorem model_zero : model 0 = Hyperboloid.origin := by
  apply Hyperboloid.ext
  rw [model_space, Hyperboloid.origin_space]
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num

def shift (r₀ : ℝ) (x : V₃) : V₃ :=
  ![x 0 - r₀, Real.exp (-r₀ / 2) * x 1, Real.exp (-r₀ / 2) * x 2]

private def shiftDerivative (r₀ : ℝ) : V₃ →L[ℝ] V₃ :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0,
      Real.exp (-r₀ / 2) • ContinuousLinearMap.proj 1,
      Real.exp (-r₀ / 2) • ContinuousLinearMap.proj 2]

private theorem hasFDerivAt_shift (r₀ : ℝ) (x : V₃) :
    HasFDerivAt (shift r₀) (shiftDerivative r₀) x := by
  have hc (i : Fin 3) := (ContinuousLinearMap.proj i : V₃ →L[ℝ] ℝ).hasFDerivAt (x := x)
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hc 0).sub_const r₀
  · exact (hc 1).const_mul (Real.exp (-r₀ / 2))
  · exact (hc 2).const_mul (Real.exp (-r₀ / 2))

private theorem contDiff_shift (r₀ : ℝ) : ContDiff ℝ ∞ (shift r₀) := by
  have hc (i : Fin 3) := (ContinuousLinearMap.proj i : V₃ →L[ℝ] ℝ).contDiff (n := ∞)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (hc 0).sub contDiff_const
  · exact (contDiff_const (c := Real.exp (-r₀ / 2))).mul (hc 1)
  · exact (contDiff_const (c := Real.exp (-r₀ / 2))).mul (hc 2)

def shiftedModel (r₀ : ℝ) : V₃ → Hyperboloid E₃ := model ∘ shift r₀

theorem contMDiff_shiftedModel (r₀ : ℝ) :
    ContMDiff 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ (shiftedModel r₀) :=
  contMDiff_model.comp (contDiff_shift r₀).contMDiff

theorem shiftedModel_base (r₀ : ℝ) :
    shiftedModel r₀ ![r₀, 0, 0] = Hyperboloid.origin := by
  have h : shift r₀ ![r₀, 0, 0] = 0 := by
    ext i
    fin_cases i <;> simp [shift]
  change model (shift r₀ ![r₀, 0, 0]) = _
  rw [h, model_zero]

theorem shiftedModel_metric (r₀ : ℝ) (x u v : V₃) :
    Hyperboloid.riemannianMetric.inner (shiftedModel r₀ x)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x u)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (shiftedModel r₀) x v) =
      (1 / 4) * (u 0 * v 0 + Real.exp (-x 0) *
        (u 1 * v 1 + u 2 * v 2)) := by
  have hshift := (hasFDerivAt_shift r₀ x).hasMFDerivAt
  have hmodel := contMDiff_model.mdifferentiableAt
    (x := shift r₀ x) (by simp)
  rw [shiftedModel, mfderiv_comp x hmodel hshift.mdifferentiableAt,
    hshift.mfderiv]
  change Hyperboloid.riemannianMetric.inner (model (shift r₀ x))
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model (shift r₀ x) (shiftDerivative r₀ u))
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model (shift r₀ x) (shiftDerivative r₀ v)) = _
  rw [model_metric]
  have he : Real.exp (-(x 0 - r₀)) * Real.exp (-r₀ / 2)^2 = Real.exp (-x 0) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change (1 / 4) * (u 0 * v 0 + Real.exp (-(x 0 - r₀)) *
    ((Real.exp (-r₀ / 2) * u 1) * (Real.exp (-r₀ / 2) * v 1) +
      (Real.exp (-r₀ / 2) * u 2) * (Real.exp (-r₀ / 2) * v 2))) = _
  calc
    _ = (1 / 4) * (u 0 * v 0 +
        (Real.exp (-(x 0 - r₀)) * Real.exp (-r₀ / 2)^2) *
          (u 1 * v 1 + u 2 * v 2)) := by ring
    _ = _ := by rw [he]

end DifferentialGeometry.Geometry.Hyperbolic.Horospherical
