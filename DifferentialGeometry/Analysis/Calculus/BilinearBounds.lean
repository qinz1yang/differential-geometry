import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_fderiv_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {f : X → E} {g : X → F} {x : X}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * (‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖) := by
  rw [B.fderiv_of_bilinear hf hg]
  apply (norm_add_le _ _).trans
  have hR := (B.precompR X).le_opNorm₂ (f x) (fderiv ℝ g x)
  have hL := (B.precompL X).le_opNorm₂ (fderiv ℝ f x) (g x)
  have hr := B.norm_precompR_le (Eₗ := X)
  have hl := B.norm_precompL_le (Eₗ := X)
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (norm_nonneg (f x))) (norm_nonneg (fderiv ℝ g x))
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hl (norm_nonneg (fderiv ℝ f x))) (norm_nonneg (g x))
  nlinarith

theorem norm_second_fderiv_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {f : X → E} {g : X → F} {x : X}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hDf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hDg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    ‖fderiv ℝ (fderiv ℝ (fun y => B (f y) (g y))) x‖ ≤
      ‖B‖ * (‖f x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ +
        2 * ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ +
        ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖g x‖) := by
  have heq : fderiv ℝ (fun y => B (f y) (g y)) =
      (fun y => B.precompR X (f y) (fderiv ℝ g y)) +
        (fun y => B.precompL X (fderiv ℝ f y) (g y)) := by
    funext y
    exact B.fderiv_of_bilinear (hf y) (hg y)
  rw [heq, fderiv_add
    ((B.precompR X).hasFDerivAt_of_bilinear (hf x).hasFDerivAt hDg.hasFDerivAt).differentiableAt
    ((B.precompL X).hasFDerivAt_of_bilinear hDf.hasFDerivAt (hg x).hasFDerivAt).differentiableAt]
  apply (norm_add_le _ _).trans
  have hr := (B.precompR X).norm_fderiv_bilinear_le (hf x) hDg
  have hl := (B.precompL X).norm_fderiv_bilinear_le hDf (hg x)
  have h1 := mul_le_mul_of_nonneg_right (B.norm_precompR_le (Eₗ := X))
    (show 0 ≤ ‖f x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ +
      ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ by positivity)
  have h2 := mul_le_mul_of_nonneg_right (B.norm_precompL_le (Eₗ := X))
    (show 0 ≤ ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ +
      ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖g x‖ by positivity)
  nlinarith

end ContinuousLinearMap
