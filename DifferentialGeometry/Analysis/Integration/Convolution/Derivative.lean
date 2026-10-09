import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution Pointwise Topology

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  [SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant]

theorem HasCompactSupport.fderiv_convolution_left_apply
    {phi f : E → Real} (hsupp : HasCompactSupport phi)
    (hphi : ContDiff Real 1 phi) (hf : LocallyIntegrable f mu) (x v : E) :
    fderiv Real (phi ⋆[ContinuousLinearMap.mul Real Real, mu] f) x v =
      ((fun y ↦ fderiv Real phi y v) ⋆[ContinuousLinearMap.mul Real Real, mu] f) x := by
  have hd := (hsupp.hasFDerivAt_convolution_left
    (ContinuousLinearMap.mul Real Real) hphi hf x).fderiv
  rw [hd]
  have hI := (hsupp.fderiv Real).convolutionExists_left
    ((ContinuousLinearMap.mul Real Real).precompL E)
    (hphi.continuous_fderiv one_ne_zero) hf x
  simp only [MeasureTheory.convolution_def]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

end NormedSpace

end
