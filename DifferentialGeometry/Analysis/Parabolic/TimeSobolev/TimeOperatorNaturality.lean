import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open MeasureTheory Filter

variable {X₁ X₂ Y₁ Y₂ : Type*}
variable [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
variable [NormedAddCommGroup X₂] [NormedSpace ℝ X₂]
variable [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
variable [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂]
variable {T : ℝ}

theorem timeOp_compLpL
    (JX : X₁ →L[ℝ] X₂) (JY : Y₁ →L[ℝ] Y₂)
    (A₁ : ℝ → X₁ →L[ℝ] Y₁)
    (hA₁ : AEStronglyMeasurable A₁ (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (A₂ : ℝ → X₂ →L[ℝ] Y₂)
    (hA₂ : AEStronglyMeasurable A₂ (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (hA : ∀ᵐ t ∂timeMeasure T, JY.comp (A₁ t) = (A₂ t).comp JX)
    (f : timeL2 X₁ T) :
    JY.compLpL 2 (timeMeasure T) (timeOp A₁ hA₁ C₁ hC₁ f) =
      timeOp A₂ hA₂ C₂ hC₂ (JX.compLpL 2 (timeMeasure T) f) := by
  apply Lp.ext
  filter_upwards [JY.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (timeOp A₁ hA₁ C₁ hC₁ f),
    timeOp_apply_ae A₁ hA₁ C₁ hC₁ f,
    timeOp_apply_ae A₂ hA₂ C₂ hC₂ (JX.compLpL 2 (timeMeasure T) f),
    JX.coeFn_compLpL (p := 2) (μ := timeMeasure T) f,
    hA] with t h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄]
  exact congrArg (fun L : X₁ →L[ℝ] Y₂ => L (f t)) h₅

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
