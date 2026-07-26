import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp

/-!
# Spatial real-power masses of the first heat-derivative majorant

This file proves that the radial first-derivative majorant belongs to every
real `L^p` class with `1 ≤ p ≤ 2`, and computes the exact parabolic scaling
of its spatial power mass.  The Koch--Lamm dual exponent lies in this range.
-/

noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The square of the time-one first-derivative majorant is integrable. -/
theorem baseD1Maj_sq_int :
    Integrable (fun x : V ↦ baseD1Maj x ^ 2) := by
  have h := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹ ^ 2)
  have heq : (fun x : V ↦ baseD1Maj x ^ 2) = fun x : V ↦
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹ ^ 2) *
        (‖x‖ ^ 2 * Real.exp (-(2 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    have hexp : (Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) ^ 2 =
        Real.exp (-(2 : ℝ)⁻¹ * ‖x‖ ^ 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    unfold baseD1Maj baseHeat
    simp only [mul_pow, hexp]
    ring
  rw [heq]
  exact h

/-- The time-one first-derivative majorant has an integrable real `p`-th
power throughout the range used by the late Koch--Lamm flux estimate. -/
theorem baseD1Maj_rpow {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Integrable (fun x : V ↦ (baseD1Maj x) ^ p) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp1
  have hmajor : Integrable (fun x : V ↦ baseD1Maj x + baseD1Maj x ^ 2) :=
    (baseD1Maj_int (V := V)).add (baseD1Maj_sq_int (V := V))
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseD1Maj baseHeat baseHeatMass
    fun_prop (disch := assumption)
  filter_upwards with x
  have hx0 : 0 ≤ baseD1Maj x := baseD1Maj_nonneg x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 p)]
  by_cases hx : baseD1Maj x ≤ 1
  · exact (Real.rpow_le_self_of_le_one hx0 hx hp1).trans
      (le_add_of_nonneg_right (sq_nonneg (baseD1Maj x)))
  · have hx1 : 1 ≤ baseD1Maj x := le_of_lt (lt_of_not_ge hx)
    have hpw : (baseD1Maj x) ^ p ≤ baseD1Maj x ^ 2 := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hx1 hp2
    exact hpw.trans (le_add_of_nonneg_left hx0)

/-- Time-one spatial mass of the real `p`-th power of the radial
first-derivative majorant. -/
def baseD1PowMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (p : ℝ) : ℝ :=
  ∫ x : V, (baseD1Maj x) ^ p

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise factorization of the scaled first-derivative majorant power. -/
theorem heatD1Maj_pow {t p : ℝ} (ht : 0 < t) (x : V) :
    (heatD1Maj t x) ^ p =
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
        (baseD1Maj ((heatScale t)⁻¹ • x)) ^ p := by
  unfold heatD1Maj
  rw [Real.mul_rpow
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD1Maj_nonneg _)]

omit [Nontrivial V] in
/-- Exact spatial integral of the scaled first-derivative majorant power. -/
theorem heatD1MajPow_int {t p : ℝ} (ht : 0 < t) :
    ∫ x : V, (heatD1Maj t x) ^ p =
      ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹) ^ p) *
        (heatScale t) ^ Module.finrank ℝ V * baseD1PowMass V p := by
  simp_rw [heatD1Maj_pow (V := V) ht]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
      (fun x : V ↦ (baseD1Maj x) ^ p) (heatScale_pos ht).le]
  simp only [smul_eq_mul, baseD1PowMass]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] in
/-- The dilation factor in `heatD1MajPow_int`, written as one power of the
heat time. -/
theorem heatD1Pow_scale {t p : ℝ} (ht : 0 < t) :
    ((((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale t)⁻¹) ^ p) *
      (heatScale t) ^ Module.finrank ℝ V =
        t ^ (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) := by
  have hs : 0 < heatScale t := heatScale_pos ht
  have hcoeff :
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ =
        (heatScale t) ^ (-(Module.finrank ℝ V + 1 : ℝ)) := by
    rw [← mul_inv, ← pow_succ]
    rw [← Real.rpow_natCast, ← Real.rpow_neg hs.le]
    congr 1
    norm_num
  rw [hcoeff]
  rw [← Real.rpow_mul hs.le]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hs]
  unfold heatScale
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul ht.le]
  congr 1
  ring

omit [Nontrivial V] in
/-- Scale-normalized form of the first-derivative majorant power mass. -/
theorem heatD1Pow_int_eq {t p : ℝ} (ht : 0 < t) :
    ∫ x : V, (heatD1Maj t x) ^ p =
      t ^ (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
        baseD1PowMass V p := by
  rw [heatD1MajPow_int (V := V) ht,
    heatD1Pow_scale (V := V) ht]

omit [Nontrivial V] in
/-- The same majorant power mass for the translated-reflected kernel used at
an observation point. -/
theorem heatD1Pow_shift {t p : ℝ} (ht : 0 < t) (x : V) :
    ∫ y : V, (heatD1Maj t (x - y)) ^ p =
      t ^ (((Module.finrank ℝ V : ℝ) * (1 - p) - p) / 2) *
        baseD1PowMass V p := by
  rw [integral_sub_left_eq_self
    (fun y : V ↦ (heatD1Maj t y) ^ p) (volume : Measure V) x]
  exact heatD1Pow_int_eq (V := V) ht

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
