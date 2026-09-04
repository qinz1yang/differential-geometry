import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Mass

noncomputable section


open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def kochLammTermMassCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (kochLammHeatExp V + 1) / (kochLammHeatExp V + 1)) *
    basePowMass V (kochLammQDual V)

def kochLammTermRoot (t : ℝ) : ℝ :=
  (kochLammTermMassCore (V := V) t) ^ (1 / kochLammQDual V)

def kochLammLate0C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  kochLammTermRoot (V := V) 1

omit [FiniteDimensional ℝ V] in
theorem kochLammTermCore_pos {t : ℝ} (ht : 0 < t) :
    0 < kochLammTermMassCore (V := V) t := by
  have ha : 0 < kochLammHeatExp V + 1 := by
    linarith [kochLammHeatExp_gt (V := V)]
  unfold kochLammTermMassCore
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos (half_pos ht) _) ha)
    (kochLammBasePow_pos (V := V) (kochLammQ_holder (V := V)).pos)

omit [FiniteDimensional ℝ V] in
theorem kochLammTermCore_scale {R : ℝ} (hR : 0 < R) :
    kochLammTermMassCore (V := V) (R ^ 2) =
      (kochLammLqScaleR (V := V) R) ^ kochLammQDual V *
        kochLammTermMassCore (V := V) 1 := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hexp :
      2 * (kochLammHeatExp V + 1) =
        (4 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammQDual V := by
    have hdiv := kochLammTermScale_exp (V := V)
    have hmul : kochLammHeatExp V + 1 =
        (2 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammQDual V :=
      (div_eq_iff hp.ne').mp hdiv
    rw [hmul]
    ring
  have hscalePow :
      (kochLammLqScaleR (V := V) R) ^ kochLammQDual V =
        R ^ ((4 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammQDual V) := by
    simpa only [kochLammLqScaleR, kochLammDim] using
      (Real.rpow_mul hR.le
        (4 / (Module.finrank ℝ V + 4 : ℝ)) (kochLammQDual V)).symm
  have hpow :
      (R ^ 2 / 2) ^ (kochLammHeatExp V + 1) =
        (kochLammLqScaleR (V := V) R) ^ kochLammQDual V *
          ((1 : ℝ) / 2) ^ (kochLammHeatExp V + 1) := by
    rw [show R ^ 2 / 2 = R ^ 2 * ((1 : ℝ) / 2) by ring]
    rw [Real.mul_rpow (sq_nonneg R) (by positivity)]
    rw [← Real.rpow_natCast_mul hR.le 2 (kochLammHeatExp V + 1)]
    rw [hscalePow]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  unfold kochLammTermMassCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

omit [FiniteDimensional ℝ V] in
theorem kochLammTermRoot_scale {R : ℝ} (hR : 0 < R) :
    kochLammTermRoot (V := V) (R ^ 2) =
      kochLammLate0C V * kochLammLqScaleR (V := V) R := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < kochLammTermMassCore (V := V) 1 :=
    kochLammTermCore_pos (V := V) one_pos
  have hpinv : kochLammQDual V * (1 / kochLammQDual V) = 1 := by
    field_simp [hp.ne']
  unfold kochLammLate0C kochLammTermRoot
  rw [kochLammTermCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc.le]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

section Measured

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem kochLammTermNorm_scale {R : ℝ} (hR : 0 < R) (x : V) :
    (kochLammTermPowMass (V := V) (R ^ 2) x) ^ (1 / kochLammQDual V) =
      kochLammLate0C V * kochLammLqScaleR (V := V) R := by
  rw [kochLammTermPowMass_eq (V := V) (sq_pos_of_pos hR) x]
  exact kochLammTermRoot_scale (V := V) hR

end Measured

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
