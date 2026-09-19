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

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
