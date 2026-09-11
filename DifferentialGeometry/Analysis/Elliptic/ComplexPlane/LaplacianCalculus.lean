import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv



noncomputable section

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem scalar_comp_partial {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hφ : DifferentiableAt ℝ φ (f z)) (v : ℂ) :
    fderiv ℝ (φ ∘ f) z v = deriv φ (f z) * fderiv ℝ f z v := by
  rw [(hφ.hasDerivAt.comp_hasFDerivAt z hf.hasFDerivAt).fderiv]
  rfl

private theorem scalar_comp_second_partial {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hφ : ContDiffAt ℝ 2 φ (f z)) (v w : ℂ) :
    fderiv ℝ (fun q => fderiv ℝ (φ ∘ f) q v) z w =
      deriv (deriv φ) (f z) * fderiv ℝ f z w * fderiv ℝ f z v +
        deriv φ (f z) * fderiv ℝ (fun q => fderiv ℝ f q v) z w := by
  have hfd := hf.differentiableAt (by norm_num)
  have hnear : (fun q => fderiv ℝ (φ ∘ f) q v) =ᶠ[𝓝 z]
      (fun q => deriv φ (f q) * fderiv ℝ f q v) := by
    filter_upwards [hf.eventually (by norm_num),
      hfd.continuousAt (hφ.eventually (by norm_num))] with q hq hφq
    change ContDiffAt ℝ 2 φ (f q) at hφq
    exact scalar_comp_partial (hq.differentiableAt (by norm_num))
      (hφq.differentiableAt (by norm_num)) v
  have hφd : DifferentiableAt ℝ (deriv φ) (f z) :=
    (hφ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpart : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [hnear.fderiv_eq]
  erw [fderiv_fun_mul (hφd.comp z hfd) hpart]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [scalar_comp_partial hfd hφd w]
  dsimp only [Function.comp_apply]
  ring



theorem laplacian_comp_scalar {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hφ : ContDiffAt ℝ 2 φ (f z)) :
    Laplacian.laplacian (φ ∘ f) z =
      deriv φ (f z) * Laplacian.laplacian f z +
        deriv (deriv φ) (f z) * ((fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) := by
  rw [← complexDivergence_gradient (hφ.comp z hf)]
  unfold complexDivergence
  rw [scalar_comp_second_partial hf hφ, scalar_comp_second_partial hf hφ]
  have hΔ := complexDivergence_gradient hf
  unfold complexDivergence at hΔ
  rw [← hΔ]
  ring



theorem laplacian_log {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) :
    Laplacian.laplacian (fun q => Real.log (f q)) z =
      Laplacian.laplacian f z / f z -
        ((fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) / (f z) ^ 2 := by
  have h := laplacian_comp_scalar hf (Real.contDiffAt_log.mpr hz)
  rw [Real.deriv_log] at h
  have hd : deriv Real.log = fun r : ℝ => r⁻¹ := by
    funext r
    exact Real.deriv_log r
  rw [hd, deriv_inv] at h
  change Laplacian.laplacian (fun q => Real.log (f q)) z = _ at h
  rw [h]
  simp only [div_eq_mul_inv]
  ring


theorem laplacian_exp {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    Laplacian.laplacian (fun q => Real.exp (f q)) z =
      Real.exp (f z) * (Laplacian.laplacian f z +
        (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) := by
  have h := laplacian_comp_scalar hf Real.contDiff_exp.contDiffAt
  simp only [Real.deriv_exp] at h
  change Laplacian.laplacian (fun q => Real.exp (f q)) z = _ at h
  rw [h]
  ring

end DifferentialGeometry.Analysis
