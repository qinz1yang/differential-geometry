import DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace DifferentialGeometry.Analysis

theorem exists_positive_triangular_decomposition
    (A : ℂ →ₗ[ℝ] ℂ) (hA : 0 < A.det) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ s b : ℝ, 0 < b ∧
      ∀ z : ℂ, A z = a * (((z + (s * z.im : ℝ)).re : ℂ) +
        (b * (z + (s * z.im : ℝ)).im) • Complex.I) := by
  have ha : A 1 ≠ 0 := by
    intro h
    rw [LinearMap.det_complex, h] at hA
    simp at hA
  let q := A Complex.I / A 1
  have hq : 0 < q.im := by
    have he : q.im = A.det / Complex.normSq (A 1) := by
      rw [LinearMap.det_complex]
      dsimp [q]
      rw [Complex.div_im]
      ring
    rw [he]
    exact div_pos hA (Complex.normSq_pos.mpr ha)
  refine ⟨A 1, ha, q.re, q.im, hq, ?_⟩
  intro z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using z.re_add_im.symm
  have hAz : A z = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
    rfl
  have hcol : A Complex.I = A 1 * q := by
    dsimp [q]
    field_simp
  rw [hAz, hcol]
  have hreal : (z + (q.re * z.im : ℝ)).re = z.re + q.re * z.im := by simp
  have himag : (z + (q.re * z.im : ℝ)).im = z.im := by simp
  rw [hreal, himag]
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
  have hqrepr := q.re_add_im
  calc
    (z.re : ℂ) * A 1 + (z.im : ℂ) * (A 1 * q) =
        A 1 * ((z.re : ℂ) + (z.im : ℂ) * ((q.re : ℂ) + q.im * Complex.I)) := by
      rw [hqrepr]
      ring
    _ = _ := by ring

end DifferentialGeometry.Analysis
