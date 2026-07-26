import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp

/-!
# Spatial real-power masses of the Euclidean heat kernel

Late-time Koch--Lamm estimates use Holder exponents strictly between one and
infinity.  This file computes the corresponding spatial kernel masses before
the remaining time integration is performed.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Exact mass of the `p`-th real power of the normalized time-one heat
kernel. -/
def basePowMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (p : ℝ) : ℝ :=
  ((baseHeatMass V)⁻¹) ^ p *
    (Real.pi / ((4 : ℝ)⁻¹ * p)) ^ (Module.finrank ℝ V / 2 : ℝ)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise normal form for a positive real power of the time-one heat
kernel. -/
theorem baseHeat_pow {p : ℝ} (_hp : 0 < p) (x : V) :
    (baseHeat x) ^ p =
      ((baseHeatMass V)⁻¹) ^ p *
        Real.exp (-((4 : ℝ)⁻¹ * p) * ‖x‖ ^ 2) := by
  unfold baseHeat
  rw [Real.mul_rpow (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
    (Real.exp_pos _).le]
  rw [← Real.exp_mul]
  congr 2
  ring

/-- A positive real power of the time-one heat kernel is integrable. -/
theorem baseHeatPow_mem {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : V => (baseHeat x) ^ p) := by
  simp_rw [baseHeat_pow (V := V) hp]
  exact (gauss_integrable (V := V)
    (mul_pos (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹) hp)).const_mul _

omit [Nontrivial V] in
/-- Exact integral of a positive real power of the time-one heat kernel. -/
theorem baseHeatPow_int {p : ℝ} (hp : 0 < p) :
    ∫ x : V, (baseHeat x) ^ p = basePowMass V p := by
  simp_rw [baseHeat_pow (V := V) hp]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (mul_pos (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹) hp)]
  rfl

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise real-power factorization of the scaled heat kernel. -/
theorem heatKernel_pow {t p : ℝ} (ht : 0 < t) (_hp : 0 < p) (x : V) :
    (heatKernel t x) ^ p =
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹) ^ p) *
        (baseHeat ((heatScale t)⁻¹ • x)) ^ p := by
  unfold heatKernel
  rw [Real.mul_rpow
    (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
    (baseHeat_nonneg _)]

/-- A positive real power of the scaled heat kernel is spatially integrable. -/
theorem heatKernelPow_mem {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    Integrable (fun x : V => (heatKernel t x) ^ p) := by
  simp_rw [heatKernel_pow (V := V) ht hp]
  exact ((baseHeatPow_mem (V := V) hp).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne')).const_mul _

omit [Nontrivial V] in
/-- Exact spatial mass of a positive real power of the scaled heat kernel. -/
theorem heatKernelPow_int {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    ∫ x : V, (heatKernel t x) ^ p =
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹) ^ p) *
        (heatScale t) ^ Module.finrank ℝ V * basePowMass V p := by
  simp_rw [heatKernel_pow (V := V) ht hp]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
      (fun x : V => (baseHeat x) ^ p) (heatScale_pos ht).le,
    baseHeatPow_int (V := V) hp]
  simp only [smul_eq_mul]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] in
/-- The dilation factor in `heatKernelPow_int`, written as one power of the
observation time. -/
theorem heatPow_scale {t p : ℝ} (ht : 0 < t) :
    ((((heatScale t) ^ Module.finrank ℝ V)⁻¹) ^ p) *
        (heatScale t) ^ Module.finrank ℝ V =
      t ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) := by
  unfold heatScale
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_neg_eq_inv_rpow]
  rw [← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
    ← Real.rpow_add ht]
  congr 1
  ring

omit [Nontrivial V] in
/-- Scale-normalized form of the exact spatial `p`-power mass. -/
theorem heatPow_int_eq {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    ∫ x : V, (heatKernel t x) ^ p =
      t ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) * basePowMass V p := by
  rw [heatKernelPow_int (V := V) ht hp, heatPow_scale (V := V) ht]

omit [Nontrivial V] in
/-- The same exact mass for the translated-reflected kernel used in a
convolution at observation point `x`. -/
theorem heatPow_shift {t p : ℝ} (ht : 0 < t) (hp : 0 < p) (x : V) :
    ∫ y : V, (heatKernel t (x - y)) ^ p =
      t ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) * basePowMass V p := by
  rw [integral_sub_left_eq_self
    (fun y : V => (heatKernel t y) ^ p) (volume : Measure V) x]
  exact heatPow_int_eq (V := V) ht hp

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
