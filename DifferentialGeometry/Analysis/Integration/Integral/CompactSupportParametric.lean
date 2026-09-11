import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex







noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]



theorem contDiffOn_planeIntegral_of_compact_support {n : ℕ∞}
    {f : P → ℂ → ℝ} {S : Set P} {K : Set ℂ} (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ p, ∀ w, p ∈ S → w ∉ K → f p w = 0)
    (hf : ContDiffOn ℝ n (fun q : P × ℂ => f q.1 q.2) (S ×ˢ univ)) :
    ContDiffOn ℝ n (fun p => ∫ w : ℂ, f p w) S := by
  have h := contDiffOn_convolution_left_with_param_comp (μ := (volume : Measure ℂ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : P => (0 : ℂ)) contDiffOn_const
    hS hK hzero (f := fun _ : ℂ => (1 : ℝ)) continuous_const.locallyIntegrable hf
  simpa only [convolution_def, ContinuousLinearMap.mul_apply', mul_one] using h

end DifferentialGeometry.Analysis
