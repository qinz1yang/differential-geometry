import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {μ : Measure ℝ} {p : ENNReal}

def rankOneAlong (u : ℝ → X) (r : ℝ → Y) (t : ℝ) : X →L[ℝ] Y :=
  (‖u t‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (r t) (u t)

theorem rankOneAlong_self
    {u : ℝ → X} {r : ℝ → Y} {t : ℝ}
    (hzero : u t = 0 → r t = 0) :
    rankOneAlong u r t (u t) = r t := by
  rw [rankOneAlong, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, real_inner_self_eq_norm_sq]
  by_cases hu : u t = 0
  · rw [hu, hzero hu, norm_zero]
    simp
  · rw [← mul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)),
      one_smul]

theorem norm_rankOneAlong_le
    {u : ℝ → X} {r : ℝ → Y} {t b : ℝ}
    (hb : 0 ≤ b) (hr : ‖r t‖ ≤ b * ‖u t‖) :
    ‖rankOneAlong u r t‖ ≤ b := by
  rw [rankOneAlong, norm_smul, InnerProductSpace.norm_rankOne]
  by_cases hu : u t = 0
  · rw [hu, norm_zero, mul_zero, mul_zero]
    exact hb
  · have hu0 : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    rw [Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
    calc
      (‖u t‖ ^ 2)⁻¹ * (‖r t‖ * ‖u t‖) ≤
          (‖u t‖ ^ 2)⁻¹ * ((b * ‖u t‖) * ‖u t‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
          (inv_nonneg.mpr (sq_nonneg _))
      _ = b := by
        calc
          (‖u t‖ ^ 2)⁻¹ * ((b * ‖u t‖) * ‖u t‖) =
              b * ((‖u t‖ ^ 2)⁻¹ * ‖u t‖ ^ 2) := by ring
          _ = b := by rw [inv_mul_cancel₀ (pow_ne_zero 2 hu0), mul_one]

theorem rankOneAlong_aesm
    {u : ℝ → X} {r : ℝ → Y}
    (hu : AEStronglyMeasurable u μ)
    (hr : AEStronglyMeasurable r μ) :
    AEStronglyMeasurable (rankOneAlong u r) μ := by
  have hdual :
      AEStronglyMeasurable (fun t => innerSL ℝ (u t)) μ :=
    (innerSL ℝ).continuous.comp_aestronglyMeasurable hu
  have hrank :
      AEStronglyMeasurable
        (fun t => InnerProductSpace.rankOne ℝ (r t) (u t)) μ := by
    have h :=
      (ContinuousLinearMap.smulRightL ℝ X Y).aestronglyMeasurable_comp₂
        hdual hr
    simpa only [InnerProductSpace.rankOne_def] using h
  have hscale :
      AEStronglyMeasurable (fun t => (‖u t‖ ^ 2)⁻¹) μ :=
    (hu.norm.pow 2).aemeasurable.inv.aestronglyMeasurable
  exact hscale.smul hrank

theorem memLp_rankOneAlong
    {u : ℝ → X} {r : ℝ → Y} {b : ℝ → ℝ}
    (hu : AEStronglyMeasurable u μ)
    (hr : AEStronglyMeasurable r μ)
    (hb : MemLp b p μ)
    (hrel : ∀ᵐ t ∂μ, ‖r t‖ ≤ |b t| * ‖u t‖) :
    MemLp (rankOneAlong u r) p μ := by
  refine hb.mono (rankOneAlong_aesm hu hr) ?_
  filter_upwards [hrel] with t ht
  simpa only [Real.norm_eq_abs] using
    norm_rankOneAlong_le (u := u) (r := r) (t := t) (abs_nonneg (b t)) ht

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
