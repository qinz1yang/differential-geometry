import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Module.Basis

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem det_smul_addHaar (b b' : Basis ι ℝ E) :
    ENNReal.ofReal |b.det b'| • b'.addHaar = b.addHaar := by
  change Real.toNNReal |b.det b'| • b'.addHaar = b.addHaar
  rw [eq_comm, b.addHaar_eq_iff]
  simp only [Measure.smul_apply, Basis.coe_parallelepiped,
    Measure.addHaar_parallelepiped,
    ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_toNNReal]
  rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b')), ← abs_mul,
    b.det_mul_det b' b, b.det_self, abs_one, ENNReal.ofReal_one]

theorem lintegral_basis_det (b b' : Basis ι ℝ E) (f : E → ENNReal) :
    (∫⁻ x, f x ∂b.addHaar) =
      ∫⁻ x, ENNReal.ofReal |b.det b'| * f x ∂b'.addHaar := by
  rw [← det_smul_addHaar b b', lintegral_smul_measure]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

end Module.Basis
