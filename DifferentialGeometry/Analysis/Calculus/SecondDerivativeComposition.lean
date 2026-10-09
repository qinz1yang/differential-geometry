import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_second_fderiv_comp_le {f : F → G} {g : E → F} {x : E}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hDf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hDg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ g)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (g x)‖ * ‖fderiv ℝ g x‖ ^ 2 +
        ‖fderiv ℝ f (g x)‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  let B := ContinuousLinearMap.compL ℝ E F G
  have heq : fderiv ℝ (f ∘ g) = fun y => B (fderiv ℝ f (g y)) (fderiv ℝ g y) := by
    funext y
    exact fderiv_comp y (hf (g y)) (hg y)
  rw [heq]
  have hh := B.norm_fderiv_bilinear_le (hDf.comp x (hg x)) hDg
  have hchain : ‖fderiv ℝ (fun y => fderiv ℝ f (g y)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (g x)‖ * ‖fderiv ℝ g x‖ := by
    change ‖fderiv ℝ (fderiv ℝ f ∘ g) x‖ ≤ _
    rw [(hDf.hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E F G
  have hb := mul_le_mul_of_nonneg_right hB
    (show 0 ≤ ‖fderiv ℝ f (g x)‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ +
      ‖fderiv ℝ (fun y => fderiv ℝ f (g y)) x‖ * ‖fderiv ℝ g x‖ by positivity)
  have hc := mul_le_mul_of_nonneg_right hchain (norm_nonneg (fderiv ℝ g x))
  simp only [Function.comp_def] at hh
  nlinarith

theorem linear_precomp_derivative_bounds (L : E →L[ℝ] F) {f : F → G}
    (hf : ContDiff ℝ 2 f) {c A B : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : ‖L‖ ≤ c) (hfirst : ∀ y, ‖fderiv ℝ f y‖ ≤ A)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ B) (x : E) :
    ‖fderiv ℝ (f ∘ L) x‖ ≤ A * c ∧
      ‖fderiv ℝ (fderiv ℝ (f ∘ L)) x‖ ≤ B * c ^ 2 := by
  have hd := hf.differentiable (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have heq : fderiv ℝ L = fun _ => L := funext fun y => L.hasFDerivAt.fderiv
  constructor
  · rw [fderiv_comp x (hd (L x)) L.differentiableAt, L.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hfirst _) hL (norm_nonneg L) hA)
  · have hh := norm_second_fderiv_comp_le hd L.differentiable (hDd (L x))
      (show DifferentiableAt ℝ (fderiv ℝ L) x by rw [heq]; exact differentiableAt_const L)
    simp only [heq, fderiv_const_apply, norm_zero, mul_zero, add_zero] at hh
    exact hh.trans (mul_le_mul (hsecond _) (sq_le_sq₀ (norm_nonneg L) hc |>.mpr hL)
      (sq_nonneg ‖L‖) hB)

end DifferentialGeometry.Analysis
