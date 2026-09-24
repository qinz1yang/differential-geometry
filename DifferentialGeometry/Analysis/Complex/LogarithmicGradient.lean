import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic

section

noncomputable section

open InnerProductSpace
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem gradient_re_eq_conj_deriv {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    gradient (fun y => (f y).re) z = conj (deriv f z) := by
  have hd := Complex.reCLM.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv
  have hmap : Complex.reCLM.comp (deriv f z • (1 : ℂ →L[ℝ] ℂ)) =
      toDual ℝ ℂ (conj (deriv f z)) := by
    ext v
    simp [toDual_apply_apply, Complex.inner, mul_comm]
  rw [hmap] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem norm_gradient_re_eq_norm_deriv {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖gradient (fun y => (f y).re) z‖ = ‖deriv f z‖ := by
  rw [gradient_re_eq_conj_deriv hf, Complex.norm_conj]

theorem gradient_log_norm_eq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    gradient (fun y => Real.log ‖f y‖) z =
      ((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z) := by
  have hd := (hasFDerivAt_log_norm_complex hz).comp z hf.hasDerivAt.complexToReal_fderiv
  have hmap : ((‖f z‖ ^ 2)⁻¹ • innerSL ℝ (f z)).comp
        (deriv f z • (1 : ℂ →L[ℝ] ℂ)) =
      toDual ℝ ℂ (((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z)) := by
    ext v
    change ((‖f z‖ ^ 2)⁻¹ : ℝ) * inner ℝ (f z) (deriv f z * v) =
      inner ℝ (((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z)) v
    rw [real_inner_smul_left]
    congr 1
    simp [Complex.inner, mul_comm, mul_assoc]
  rw [hmap] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem norm_deriv_eq_norm_mul_norm_gradient_log_norm {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    ‖deriv f z‖ = ‖f z‖ * ‖gradient (fun y => Real.log ‖f y‖) z‖ := by
  rw [gradient_log_norm_eq hf hz, norm_smul, norm_mul, Complex.norm_conj,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hnorm : ‖f z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp [hnorm]

end DifferentialGeometry.Analysis

end

end
