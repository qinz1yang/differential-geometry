import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod



noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

theorem volume_complex_re_eq (a : ℝ) : volume {z : ℂ | z.re = a} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton a).prod (MeasurableSet.univ (α := ℝ))).nullMeasurableSet
  have he : Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (univ : Set ℝ)) = {z : ℂ | z.re = a} := by
    ext z
    simp
  rw [he] at h
  simpa only [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul] using h

theorem volume_complex_im_eq (a : ℝ) : volume {z : ℂ | z.im = a} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((MeasurableSet.univ (α := ℝ)).prod (measurableSet_singleton a)).nullMeasurableSet
  have he : Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ {a}) = {z : ℂ | z.im = a} := by
    ext z
    simp
  rw [he] at h
  simpa only [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero] using h

theorem ae_complex_re_ne (a : ℝ) : ∀ᵐ z : ℂ, z.re ≠ a := by
  rw [ae_iff]
  convert volume_complex_re_eq a using 1
  congr 1
  ext z
  simp

theorem ae_complex_im_ne (a : ℝ) : ∀ᵐ z : ℂ, z.im ≠ a := by
  rw [ae_iff]
  convert volume_complex_im_eq a using 1
  congr 1
  ext z
  simp

end DifferentialGeometry.Analysis
