import DifferentialGeometry.Tensor.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

namespace LinearMap.BilinForm

theorem sqrt_det_toMatrix_basis_change
    {E i : Type*} [AddCommGroup E] [Module Real E]
    [Fintype i] [DecidableEq i] (B : LinearMap.BilinForm Real E) (b c : Module.Basis i Real E) :
    Real.sqrt (toMatrix c B).det = |b.det c| * Real.sqrt (toMatrix b B).det := by
  rw [B.det_toMatrix_basis_change b c, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem sqrt_det_smul_addHaar_eq
    {E i : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] [Fintype i] [DecidableEq i]
    (B : LinearMap.BilinForm Real E) (b c : Module.Basis i Real E) :
    ENNReal.ofReal (Real.sqrt (toMatrix b B).det) • b.addHaar =
      ENNReal.ofReal (Real.sqrt (toMatrix c B).det) • c.addHaar := by
  rw [B.sqrt_det_toMatrix_basis_change b c, ENNReal.ofReal_mul (abs_nonneg _),
    mul_comm, mul_smul, Module.Basis.det_smul_addHaar]

end LinearMap.BilinForm
