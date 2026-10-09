/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.MetricAlgebra
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.Horospherical

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V₃" => Fin 3 → ℝ
local notation "V₄" => Fin 4 → ℝ

private def timeProjection : V₄ →L[ℝ] ℝ := ContinuousLinearMap.proj 0

private def spaceProjection : V₄ →L[ℝ] E₃ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2,
        ContinuousLinearMap.proj 3])

private theorem spaceProjection_inner (a b : V₄) :
    inner ℝ (spaceProjection a) (spaceProjection b) =
      a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  change inner ℝ (WithLp.toLp 2 ![a 1, a 2, a 3])
    (WithLp.toLp 2 ![b 1, b 2, b 3]) = _
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (congrArg₂ (fun x y : ℝ => x + y)
      (Real.inner_apply (a 1) (b 1)) (Real.inner_apply (a 2) (b 2)))
    (Real.inner_apply (a 3) (b 3))

private theorem lorentzPair_projections (a b : V₄) :
    -(timeProjection a * timeProjection b) +
      inner ℝ (spaceProjection a) (spaceProjection b) = lorentzPair a b := by
  rw [spaceProjection_inner]
  change -(a 0 * b 0) + (a 1 * b 1 + a 2 * b 2 + a 3 * b 3) = _
  unfold lorentzPair
  ring

private theorem metric_inner_time_space (p : Hyperboloid E₃)
    (v w : TangentSpace 𝓘(ℝ, E₃) p) :
    Hyperboloid.riemannianMetric.inner p v w =
      -(mvfderiv 𝓘(ℝ, E₃) Hyperboloid.time p v *
        mvfderiv 𝓘(ℝ, E₃) Hyperboloid.time p w) +
      inner ℝ (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p v)
        (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p w) := by
  have ht (u : TangentSpace 𝓘(ℝ, E₃) p) :
      mvfderiv 𝓘(ℝ, E₃) Hyperboloid.time p u =
        inner ℝ p.space
          (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p u) / p.time :=
    Hyperboloid.mfderiv_time_apply p u
  rw [Hyperboloid.riemannianMetric_inner, ht v, ht w, ← p.time_sq]
  change inner ℝ (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p v)
      (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p w) -
    inner ℝ p.space (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p v) *
      inner ℝ p.space (mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph p w) / p.time^2 = _
  field_simp [p.time_pos.ne']
  ring

theorem metric_inner_comp (P : V₃ → Hyperboloid E₃) (x u v : V₃)
    (hP : MDifferentiableAt 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x) :
    Hyperboloid.riemannianMetric.inner (P x)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x u)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x v) =
      -(fderiv ℝ (Hyperboloid.time ∘ P) x u *
        fderiv ℝ (Hyperboloid.time ∘ P) x v) +
      inner ℝ (fderiv ℝ (Hyperboloid.spaceDiffeomorph ∘ P) x u)
        (fderiv ℝ (Hyperboloid.spaceDiffeomorph ∘ P) x v) := by
  have ht := (Hyperboloid.contMDiff_time (E := E₃) (n := ∞)).mdifferentiableAt
    (x := P x) (by simp)
  have hs := (Hyperboloid.contMDiff_space (E := E₃) (n := ∞)).mdifferentiableAt
    (x := P x) (by simp)
  have htime (z : TangentSpace 𝓘(ℝ, V₃) x) :
      mvfderiv 𝓘(ℝ, E₃) Hyperboloid.time (P x)
        (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x z) =
          fderiv ℝ (Hyperboloid.time ∘ P) x z := by
    exact (mvfderiv_comp_apply x ht hP z).symm.trans
      (congrArg (fun L : TangentSpace 𝓘(ℝ, V₃) x →L[ℝ] ℝ => L z)
        (mvfderiv_eq_fderiv (f := Hyperboloid.time ∘ P) (x := x)))
  have hspace (z : TangentSpace 𝓘(ℝ, V₃) x) :
      mvfderiv 𝓘(ℝ, E₃) Hyperboloid.spaceDiffeomorph (P x)
        (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x z) =
          fderiv ℝ (Hyperboloid.spaceDiffeomorph ∘ P) x z := by
    exact (mvfderiv_comp_apply x hs hP z).symm.trans
      (congrArg (fun L : TangentSpace 𝓘(ℝ, V₃) x →L[ℝ] E₃ => L z)
        (mvfderiv_eq_fderiv (f := Hyperboloid.spaceDiffeomorph ∘ P) (x := x)))
  exact (metric_inner_time_space (P x)
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x u)
    (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x v)).trans
      (congrArg₂ (fun a b : ℝ => a + b)
        (congrArg Neg.neg (congrArg₂ (fun a b : ℝ => a * b) (htime u) (htime v)))
        (congrArg₂ (inner ℝ) (hspace u) (hspace v)))

theorem metric_inner_of_warped_coordinates
    (P : V₃ → Hyperboloid E₃)
    (hP : ContMDiff 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ P)
    (ht : Hyperboloid.time ∘ P = timeProjection ∘ warpedPoint)
    (hs : Hyperboloid.spaceDiffeomorph ∘ P = spaceProjection ∘ warpedPoint)
    (x u v : V₃) :
    Hyperboloid.riemannianMetric.inner (P x)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x u)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) P x v) =
      (1 / 4) * (u 0 * v 0 + Real.exp (-x 0) *
        (u 1 * v 1 + u 2 * v 2)) := by
  have hd : HasFDerivAt warpedPoint
      ((differential (warpCoordinates x)).comp (warpDifferential x)) x :=
    (hasFDerivAt_point (warpCoordinates x) (Real.exp_ne_zero _)).comp x
      (hasFDerivAt_warpCoordinates x)
  rw [metric_inner_comp P x u v (hP.mdifferentiableAt (by simp)), ht, hs,
    (timeProjection.hasFDerivAt.comp x hd).fderiv,
    (spaceProjection.hasFDerivAt.comp x hd).fderiv]
  have h := lorentzPair_fderiv_warpedPoint x u v
  rw [fderiv_warpedPoint] at h
  exact (lorentzPair_projections
    ((differential (warpCoordinates x)).comp (warpDifferential x) u)
    ((differential (warpCoordinates x)).comp (warpDifferential x) v)).trans h

private theorem contDiff_warpedPoint : ContDiff ℝ ∞ warpedPoint := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun x : V₃ => x i) :=
    (ContinuousLinearMap.proj i : V₃ →L[ℝ] ℝ).contDiff
  have he : ContDiff ℝ ∞ (fun x : V₃ => Real.exp (-x 0 / 2)) :=
    Real.contDiff_exp.comp ((hc 0).neg.div_const 2)
  have hi : ContDiff ℝ ∞ (fun x : V₃ => (Real.exp (-x 0 / 2))⁻¹) :=
    he.inv (fun x => Real.exp_ne_zero _)
  have hq : ContDiff ℝ ∞ (fun x : V₃ => (x 1)^2 + (x 2)^2) :=
    ((hc 1).pow 2).add ((hc 2).pow 2)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : V₃ =>
      (1 / 2) * Real.exp (-x 0 / 2) + (1 / 2) * (Real.exp (-x 0 / 2))⁻¹ +
        (1 / 8) * Real.exp (-x 0 / 2) * ((x 1)^2 + (x 2)^2))
    exact (((contDiff_const (c := (1 / 2 : ℝ))).mul he).add
      ((contDiff_const (c := (1 / 2 : ℝ))).mul hi)).add
      (((contDiff_const (c := (1 / 8 : ℝ))).mul he).mul hq)
  · change ContDiff ℝ ∞ (fun x : V₃ =>
      (-1 / 2) * Real.exp (-x 0 / 2) + (1 / 2) * (Real.exp (-x 0 / 2))⁻¹ +
        (1 / 8) * Real.exp (-x 0 / 2) * ((x 1)^2 + (x 2)^2))
    exact (((contDiff_const (c := (-1 / 2 : ℝ))).mul he).add
      ((contDiff_const (c := (1 / 2 : ℝ))).mul hi)).add
      (((contDiff_const (c := (1 / 8 : ℝ))).mul he).mul hq)
  · exact ((contDiff_const (c := (1 / 2 : ℝ))).mul he).mul (hc 1)
  · exact ((contDiff_const (c := (1 / 2 : ℝ))).mul he).mul (hc 2)

private theorem warpedPoint_time_pos (x : V₃) : 0 < timeProjection (warpedPoint x) := by
  change 0 < (1 / 2) * Real.exp (-x 0 / 2) +
    (1 / 2) * (Real.exp (-x 0 / 2))⁻¹ +
    (1 / 8) * Real.exp (-x 0 / 2) * ((x 1)^2 + (x 2)^2)
  positivity

private theorem warpedPoint_time_sq (x : V₃) :
    (timeProjection (warpedPoint x))^2 = 1 + ‖spaceProjection (warpedPoint x)‖^2 := by
  rw [← real_inner_self_eq_norm_sq, spaceProjection_inner]
  let h := Real.exp (-x 0 / 2)
  let q := (x 1)^2 + (x 2)^2
  change ((1 / 2) * h + (1 / 2) * h⁻¹ + (1 / 8) * h * q)^2 =
    1 + (((-1 / 2) * h + (1 / 2) * h⁻¹ + (1 / 8) * h * q) *
      ((-1 / 2) * h + (1 / 2) * h⁻¹ + (1 / 8) * h * q) +
      ((1 / 2) * h * x 1) * ((1 / 2) * h * x 1) +
      ((1 / 2) * h * x 2) * ((1 / 2) * h * x 2))
  dsimp [q]
  field_simp [show h ≠ 0 from Real.exp_ne_zero _]
  ring

def model : V₃ → Hyperboloid E₃ :=
  fun x => Hyperboloid.ofSpace (spaceProjection (warpedPoint x))

theorem contMDiff_model : ContMDiff 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ model :=
  Hyperboloid.contMDiff_ofSpace.comp
    (spaceProjection.contDiff.comp contDiff_warpedPoint).contMDiff

private theorem model_time (x : V₃) : (model x).time = timeProjection (warpedPoint x) := by
  have hs := (model x).time_sq
  have hp := (model x).time_pos
  have hr := warpedPoint_time_sq x
  have ht := warpedPoint_time_pos x
  change (model x).time^2 = 1 + ‖spaceProjection (warpedPoint x)‖^2 at hs
  nlinarith

theorem model_metric (x u v : V₃) :
    Hyperboloid.riemannianMetric.inner (model x)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x u)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) model x v) =
      (1 / 4) * (u 0 * v 0 + Real.exp (-x 0) *
        (u 1 * v 1 + u 2 * v 2)) :=
  metric_inner_of_warped_coordinates model contMDiff_model
    (funext model_time) rfl x u v

theorem model_slice_injective (r : ℝ) :
    Function.Injective (fun z : Fin 2 → ℝ => model ![r, z 0, z 1]) := by
  intro a b hab
  have h₁ := congrArg (fun p : Hyperboloid E₃ => p.space 1) hab
  have h₂ := congrArg (fun p : Hyperboloid E₃ => p.space 2) hab
  change (1 / 2) * Real.exp (-r / 2) * a 0 =
    (1 / 2) * Real.exp (-r / 2) * b 0 at h₁
  change (1 / 2) * Real.exp (-r / 2) * a 1 =
    (1 / 2) * Real.exp (-r / 2) * b 1 at h₂
  have hc : (1 / 2 : ℝ) * Real.exp (-r / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.exp_ne_zero _)
  have h₁' := mul_left_cancel₀ hc h₁
  have h₂' := mul_left_cancel₀ hc h₂
  funext i
  fin_cases i
  · exact h₁'
  · exact h₂'

end DifferentialGeometry.Geometry.Hyperbolic.Horospherical
