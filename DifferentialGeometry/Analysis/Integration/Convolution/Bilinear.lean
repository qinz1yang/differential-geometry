import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem integral_normed_bilinear_apply
    (φ : ContDiffBump (0 : E)) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : LocallyIntegrable B μ) (x v w : E) :
    ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] B) x) v w =
      ∫ t, φ.normed μ t * B (x - t) v w ∂μ := by
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  have hi : Integrable (fun t => φ.normed μ t • B (x - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hB x
  change ev (∫ t, φ.normed μ t • B (x - t) ∂μ) = _
  rw [← ev.integral_comp_comm hi]
  rfl

theorem normed_convolution_bilinear_symmetric
    (φ : ContDiffBump (0 : E)) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : LocallyIntegrable B μ) (hsymm : ∀ x v w, B x v w = B x w v) (x v w : E) :
    ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] B) x) v w =
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] B) x) w v := by
  rw [integral_normed_bilinear_apply φ hB, integral_normed_bilinear_apply φ hB]
  congr 1
  funext t
  rw [hsymm]

theorem normed_convolution_bilinear_quadratic_bounds
    (φ : ContDiffBump (0 : E)) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : LocallyIntegrable B μ) (lower upper : ℝ)
    (hbound : ∀ x v, lower * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ upper * ‖v‖ ^ 2)
    (x v : E) :
    lower * ‖v‖ ^ 2 ≤ ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] B) x) v v ∧
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] B) x) v v ≤ upper * ‖v‖ ^ 2 := by
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  have hi : Integrable (fun t => φ.normed μ t • B (x - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hB x
  have heval : Integrable (fun t => φ.normed μ t * B (x - t) v v) μ := by
    simpa only [Function.comp_def, map_smul, ev, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul] using ev.integrable_comp hi
  rw [integral_normed_bilinear_apply φ hB]
  constructor
  · calc
      lower * ‖v‖ ^ 2 = ∫ t, φ.normed μ t * (lower * ‖v‖ ^ 2) ∂μ := by
        rw [integral_mul_const, φ.integral_normed, one_mul]
      _ ≤ ∫ t, φ.normed μ t * B (x - t) v v ∂μ :=
        integral_mono (φ.integrable_normed.mul_const _) heval
          (fun t => mul_le_mul_of_nonneg_left (hbound (x - t) v).1 (φ.nonneg_normed t))
  · calc
      (∫ t, φ.normed μ t * B (x - t) v v ∂μ) ≤
          ∫ t, φ.normed μ t * (upper * ‖v‖ ^ 2) ∂μ :=
        integral_mono heval (φ.integrable_normed.mul_const _)
          (fun t => mul_le_mul_of_nonneg_left (hbound (x - t) v).2 (φ.nonneg_normed t))
      _ = upper * ‖v‖ ^ 2 := by
        rw [integral_mul_const, φ.integral_normed, one_mul]

end ContDiffBump
