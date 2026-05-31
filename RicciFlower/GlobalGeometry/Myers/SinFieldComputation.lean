import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Myers sine-field computation

This file contains the pure real-analysis part of the Myers index-form
comparison: the scaled `sin^2`/`cos^2` integrals and the resulting integral
upper bound from a pointwise Ricci lower-bound function.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Real intervalIntegral
open scoped Real

/-- `∫₀^L sin²(π t / L) dt = L / 2` for `L ≠ 0`. -/
theorem integral_sin_sq_piL {L : ℝ} (hL : L ≠ 0) :
    (∫ t in (0 : ℝ)..L, Real.sin (Real.pi / L * t) ^ 2) = L / 2 := by
  have hc : Real.pi / L ≠ 0 := div_ne_zero Real.pi_ne_zero hL
  have hsubst :=
    intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := L) (c := Real.pi / L)
      (f := fun u : ℝ => Real.sin u ^ 2) hc
  have hendpoint : Real.pi / L * L = Real.pi := by
    field_simp [hL]
  calc
    (∫ t in (0 : ℝ)..L, Real.sin (Real.pi / L * t) ^ 2)
        = (Real.pi / L)⁻¹ •
            (∫ u in (Real.pi / L) * 0..(Real.pi / L) * L,
              Real.sin u ^ 2) := by
          simpa using hsubst
    _ = (Real.pi / L)⁻¹ * (∫ u in (0 : ℝ)..Real.pi, Real.sin u ^ 2) := by
          simp [hendpoint, smul_eq_mul]
    _ = (Real.pi / L)⁻¹ * (Real.pi / 2) := by
          simp [integral_sin_sq]
    _ = L / 2 := by
          field_simp [hL, Real.pi_ne_zero]

/-- `∫₀^L cos²(π t / L) dt = L / 2` for `L ≠ 0`. -/
theorem integral_cos_sq_piL {L : ℝ} (hL : L ≠ 0) :
    (∫ t in (0 : ℝ)..L, Real.cos (Real.pi / L * t) ^ 2) = L / 2 := by
  have hc : Real.pi / L ≠ 0 := div_ne_zero Real.pi_ne_zero hL
  have hsubst :=
    intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := L) (c := Real.pi / L)
      (f := fun u : ℝ => Real.cos u ^ 2) hc
  have hendpoint : Real.pi / L * L = Real.pi := by
    field_simp [hL]
  calc
    (∫ t in (0 : ℝ)..L, Real.cos (Real.pi / L * t) ^ 2)
        = (Real.pi / L)⁻¹ •
            (∫ u in (Real.pi / L) * 0..(Real.pi / L) * L,
              Real.cos u ^ 2) := by
          simpa using hsubst
    _ = (Real.pi / L)⁻¹ * (∫ u in (0 : ℝ)..Real.pi, Real.cos u ^ 2) := by
          simp [hendpoint, smul_eq_mul]
    _ = (Real.pi / L)⁻¹ * (Real.pi / 2) := by
          simp [integral_cos_sq]
    _ = L / 2 := by
          field_simp [hL, Real.pi_ne_zero]

/-- Core Myers inequality (pure analysis). Once the summed index form is written
as `∫₀^L [(n-1)(π/L)^2 cos²(πt/L) - sin²(πt/L) * r t] dt`, a pointwise Ricci
lower bound `r >= (n-1)k` on `[0,L]` gives the standard upper estimate. -/
theorem sum_indexForm_integral_le
    {L k : ℝ} {n : ℕ} (hL : 0 < L) (r : ℝ → ℝ)
    (hr_cont : ContinuousOn r (Set.Icc (0 : ℝ) L))
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) L, ((n : ℝ) - 1) * k ≤ r t) :
    (∫ t in (0 : ℝ)..L,
        ((n : ℝ) - 1) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2
          - Real.sin (Real.pi / L * t) ^ 2 * r t)
      ≤ ((n : ℝ) - 1) * (L / 2) * ((Real.pi / L) ^ 2 - k) := by
  let A : ℝ := ((n : ℝ) - 1) * (Real.pi / L) ^ 2
  let B : ℝ := ((n : ℝ) - 1) * k
  let f : ℝ → ℝ := fun t =>
    A * Real.cos (Real.pi / L * t) ^ 2 -
      Real.sin (Real.pi / L * t) ^ 2 * r t
  let g : ℝ → ℝ := fun t =>
    A * Real.cos (Real.pi / L * t) ^ 2 -
      B * Real.sin (Real.pi / L * t) ^ 2
  have htrigCont :
      Continuous fun t : ℝ => Real.sin (Real.pi / L * t) ^ 2 := by
    fun_prop
  have hcosCont :
      Continuous fun t : ℝ => Real.cos (Real.pi / L * t) ^ 2 := by
    fun_prop
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) L) := by
    dsimp [f]
    exact (hcosCont.continuousOn.const_mul A).sub
      (htrigCont.continuousOn.mul hr_cont)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) L) := by
    dsimp [g]
    exact (hcosCont.continuousOn.const_mul A).sub
      (htrigCont.continuousOn.const_mul B)
  have hmono : ∀ t ∈ Set.Icc (0 : ℝ) L, f t ≤ g t := by
    intro t ht
    dsimp [f, g]
    have hsin_nonneg : 0 ≤ Real.sin (Real.pi / L * t) ^ 2 := sq_nonneg _
    have hmul :
        Real.sin (Real.pi / L * t) ^ 2 * B ≤
          Real.sin (Real.pi / L * t) ^ 2 * r t :=
      mul_le_mul_of_nonneg_left (hr t ht) hsin_nonneg
    have hmul' :
        B * Real.sin (Real.pi / L * t) ^ 2 ≤
          Real.sin (Real.pi / L * t) ^ 2 * r t := by
      simpa [mul_comm] using hmul
    linarith
  have h_int_le :
      (∫ t in (0 : ℝ)..L, f t) ≤ ∫ t in (0 : ℝ)..L, g t := by
    exact intervalIntegral.integral_mono_on hL.le
      (hf_cont.intervalIntegrable_of_Icc hL.le)
      (hg_cont.intervalIntegrable_of_Icc hL.le)
      hmono
  have hcos_eval :
      (∫ t in (0 : ℝ)..L, Real.cos (Real.pi / L * t) ^ 2) = L / 2 :=
    integral_cos_sq_piL hL.ne'
  have hsin_eval :
      (∫ t in (0 : ℝ)..L, Real.sin (Real.pi / L * t) ^ 2) = L / 2 :=
    integral_sin_sq_piL hL.ne'
  have hg_eval :
      (∫ t in (0 : ℝ)..L, g t) =
        A * (L / 2) - B * (L / 2) := by
    dsimp [g]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hcos_eval, hsin_eval]
    · exact hcosCont.intervalIntegrable (0 : ℝ) L |>.const_mul A
    · exact htrigCont.intervalIntegrable (0 : ℝ) L |>.const_mul B
  calc
    (∫ t in (0 : ℝ)..L,
        ((n : ℝ) - 1) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2
          - Real.sin (Real.pi / L * t) ^ 2 * r t)
        = ∫ t in (0 : ℝ)..L, f t := by
          rfl
    _ ≤ ∫ t in (0 : ℝ)..L, g t := h_int_le
    _ = A * (L / 2) - B * (L / 2) := hg_eval
    _ = ((n : ℝ) - 1) * (L / 2) * ((Real.pi / L) ^ 2 - k) := by
          dsimp [A, B]
          ring

end Myers
end GlobalGeometry
end RicciFlower
