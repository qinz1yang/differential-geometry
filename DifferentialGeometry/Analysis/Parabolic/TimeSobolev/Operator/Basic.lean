import DifferentialGeometry.Analysis.Integration.Lp.Operator
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T : ℝ}

theorem memLp_timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    MemLp (fun t => A t (f t)) 2 (timeMeasure T) :=
  (Lp.memLp f).clm_apply_of_bound A (fun v => hA.apply_continuousLinearMap v) hC

noncomputable def timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    timeL2 X T →L[ℝ] timeL2 Y T :=
  Lp.multiplicationOperator A (fun v => hA.apply_continuousLinearMap v) C hC

theorem timeOp_apply_ae
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    timeOp A hA C hC f =ᵐ[timeMeasure T] fun t => A t (f t) :=
  Lp.multiplicationOperator_apply_ae A (fun v => hA.apply_continuousLinearMap v) C hC f

theorem timeOp_norm_le
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA C hC‖ ≤ (C : ℝ) :=
  Lp.multiplicationOperator_norm_le A (fun v => hA.apply_continuousLinearMap v) C hC

theorem timeOp_sub
    (A B : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    timeOp A hA CA hCA - timeOp B hB CB hCB =
      timeOp (fun t ↦ A t - B t) (hA.sub hB) C hC := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeOp A hA CA hCA f) (timeOp B hB CB hCB f),
    timeOp_apply_ae A hA CA hCA f, timeOp_apply_ae B hB CB hCB f,
    timeOp_apply_ae (fun t ↦ A t - B t) (hA.sub hB) C hC f]
    with t hsub hAf hBf hDf
  change ((timeOp A hA CA hCA f - timeOp B hB CB hCB f : timeL2 Y T) : ℝ → Y) t = _
  rw [hsub, Pi.sub_apply, hAf, hBf, hDf, sub_apply]

theorem timeOp_sub_norm_le
    (A B : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA CA hCA - timeOp B hB CB hCB‖ ≤ (C : ℝ) := by
  rw [timeOp_sub A B hA hB CA CB C hCA hCB hC]
  exact timeOp_norm_le _ _ C hC


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
