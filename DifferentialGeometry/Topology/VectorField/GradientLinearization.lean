import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.VectorField.VerticalLinearization
import DifferentialGeometry.Tensor.QuadraticForm.SignatureDeterminant

set_option autoImplicit false
noncomputable section
open InnerProductSpace Bundle
open scoped Manifold ContDiff
namespace Poincare.VectorField
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {x : E}


theorem contDiffAt_gradient (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (gradient f) x := by
  exact ((toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp x
    (hf.fderiv_right (by norm_num))


theorem fderiv_gradient (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (gradient f) x =
      (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ f) x := by
  exact (((toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt).comp x
    ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt one_ne_zero).hasFDerivAt).fderiv


theorem inner_fderiv_gradient (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    inner ℝ (fderiv ℝ (gradient f) x v) w = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_gradient hf]
  change inner ℝ ((toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v)) w = _
  rw [← toDual_apply_apply (𝕜 := ℝ), (toDual ℝ E).apply_symm_apply]


theorem isSymmetric_fderiv_gradient (hf : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (fderiv ℝ (gradient f) x v) w = inner ℝ v (fderiv ℝ (gradient f) x w)
  rw [inner_fderiv_gradient hf, real_inner_comm, inner_fderiv_gradient hf]
  exact hf.isSymmSndFDerivAt (by norm_num) v w


theorem contMDiffAt_gradient_section (hf : ContDiffAt ℝ 2 f x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y : E => (⟨y, (gradient f y : E)⟩ : TangentBundle 𝓘(ℝ, E) E)) x := by
  erw [contMDiffAt_section]
  simpa only [trivializationAt_model_space_apply] using!
    (contDiffAt_gradient hf).contMDiffAt


theorem gradient_eq_zero_iff : gradient f x = 0 ↔ fderiv ℝ f x = 0 := by
  rw [gradient, (toDual ℝ E).symm.map_eq_zero_iff]


theorem linearizationAtZero_gradient (hf : ContDiffAt ℝ 2 f x)
    (hcrit : fderiv ℝ f x = 0) :
    linearizationAtZero ((contMDiffAt_gradient_section hf).mdifferentiableAt one_ne_zero)
        ((gradient_eq_zero_iff (f := f) (x := x)).mpr hcrit) =
      (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ f) x := by
  erw [linearizationAtZero_modelSpace_eq_fderiv]
  exact fderiv_gradient hf

end Hilbert

section Hessian
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}


theorem chartHessianAt_eq_operatorForm (hf : ContDiffAt ℝ 2 f x) :
    DifferentialGeometry.Topology.Morse.chartHessianAt f x =
      Poincare.QuadraticForm.operatorForm (fderiv ℝ (gradient f) x).toLinearMap := by
  ext v
  exact (inner_fderiv_gradient hf v v).symm

variable [FiniteDimensional ℝ E]


theorem det_fderiv_gradient_ne_zero (hf : ContDiffAt ℝ 2 f x)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt f x)).SeparatingLeft) :
    LinearMap.det (fderiv ℝ (gradient f) x).toLinearMap ≠ 0 := by
  rw [chartHessianAt_eq_operatorForm hf] at hnd
  exact (Poincare.QuadraticForm.operatorForm_separatingLeft_iff
    (isSymmetric_fderiv_gradient hf)).mp hnd


theorem sign_det_fderiv_gradient (hf : ContDiffAt ℝ 2 f x)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt f x)).SeparatingLeft) :
    (SignType.sign (LinearMap.det (fderiv ℝ (gradient f) x).toLinearMap) : ℤ) =
      (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt f x) := by
  rw [chartHessianAt_eq_operatorForm hf]
  exact Poincare.QuadraticForm.sign_det_eq_neg_one_pow_sigNeg
    (isSymmetric_fderiv_gradient hf) (det_fderiv_gradient_ne_zero hf hnd)

end Hessian
end Poincare.VectorField
