import DifferentialGeometry.Analysis.Complex.Beltrami.Coefficient
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv

section

noncomputable section
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

def complexLinearPart (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 - Complex.I * L Complex.I) / 2

def complexAntilinearPart (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 + Complex.I * L Complex.I) / 2

theorem apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj
    (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = complexLinearPart L * z + complexAntilinearPart L * conj z := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [complexLinearPart, complexAntilinearPart, Complex.mul_re, Complex.mul_im,
      Complex.real_smul] <;> ring

theorem beltrami_eq_iff_complex_linear_factor (L : ℂ →L[ℝ] ℂ) (μ : ℂ) :
    complexAntilinearPart L = μ * complexLinearPart L ↔
      ∀ z : ℂ, L z = complexLinearPart L * (z + μ * conj z) := by
  constructor
  · intro h z
    rw [apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj, h]
    ring
  · intro h
    have h1 := h 1
    have hI := h Complex.I
    have ha : complexAntilinearPart L = (L 1 + Complex.I * L Complex.I) / 2 := rfl
    rw [ha, h1, hI]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

theorem complexLinearPart_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    complexLinearPart (c • L) = c * complexLinearPart L := by
  simp only [complexLinearPart, smul_apply, smul_eq_mul]
  ring

theorem complexAntilinearPart_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPart (c • L) = c * complexAntilinearPart L := by
  simp only [complexAntilinearPart, smul_apply, smul_eq_mul]
  ring

theorem beltrami_fderiv_comp_holomorphic
    {W F : ℂ → ℂ} {z μ : ℂ} (hW : DifferentiableAt ℝ W z)
    (hF : DifferentiableAt ℂ F (W z))
    (hBel : complexAntilinearPart (fderiv ℝ W z) = μ * complexLinearPart (fderiv ℝ W z)) :
    complexAntilinearPart (fderiv ℝ (fun w => F (W w)) z) =
      μ * complexLinearPart (fderiv ℝ (fun w => F (W w)) z) := by
  have hh := (hF.hasDerivAt.complexToReal_fderiv.comp z hW.hasFDerivAt).fderiv
  have heq : fderiv ℝ (fun w => F (W w)) z = deriv F (W z) • fderiv ℝ W z := by
    change fderiv ℝ (fun w => F (W w)) z = _ at hh
    rw [hh]
    ext v
    simp
  rw [heq, complexAntilinearPart_smul, complexLinearPart_smul, hBel]
  ring

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem complexLinearPart_ne_zero_of_beltrami_of_ne_zero
    {L : ℂ →L[ℝ] ℂ} {μ : ℂ} (hL : L ≠ 0)
    (hBel : complexAntilinearPart L = μ * complexLinearPart L) : complexLinearPart L ≠ 0 := by
  intro ha
  apply hL
  ext z
  rw [apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj, hBel, ha]
  simp

theorem apply_eq_smul_of_same_beltrami
    (L K : ℂ →L[ℝ] ℂ) {μ : ℂ} (hK : K ≠ 0)
    (hLBel : complexAntilinearPart L = μ * complexLinearPart L)
    (hKBel : complexAntilinearPart K = μ * complexLinearPart K) (z : ℂ) :
    L z = (complexLinearPart L / complexLinearPart K) * K z := by
  have hα := complexLinearPart_ne_zero_of_beltrami_of_ne_zero hK hKBel
  rw [(beltrami_eq_iff_complex_linear_factor L μ).mp hLBel z,
    (beltrami_eq_iff_complex_linear_factor K μ).mp hKBel z]
  field_simp

theorem comp_inverse_apply_eq_mul_of_same_beltrami
    (L : ℂ →L[ℝ] ℂ) (K : ℂ ≃L[ℝ] ℂ) {μ : ℂ}
    (hLBel : complexAntilinearPart L = μ * complexLinearPart L)
    (hKBel : complexAntilinearPart K.toContinuousLinearMap =
      μ * complexLinearPart K.toContinuousLinearMap) (z : ℂ) :
    L (K.symm z) = (complexLinearPart L / complexLinearPart K.toContinuousLinearMap) * z := by
  have hK : K.toContinuousLinearMap ≠ 0 := by
    intro hz
    have hh : K (1 : ℂ) = K 0 := by rw [map_zero]; exact congrArg (fun k : ℂ →L[ℝ] ℂ => k 1) hz
    exact one_ne_zero (K.injective hh)
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
    apply_eq_smul_of_same_beltrami L K.toContinuousLinearMap hK hLBel hKBel (K.symm z)

end DifferentialGeometry.Analysis

end

end
