import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateMass

/-!
# Radius scaling of the terminal Koch--Lamm kernel norm

This file isolates the real-power algebra after the exact terminal kernel
mass calculation.  At observation time `t = R^2`, the Hölder-dual kernel
norm has exactly the factor `R^(4/(n+4))` needed to cancel the inverse scale
in `KLSource0.late_lq`.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Scalar mass factor in `klTermPowMass_eq`, before taking the Hölder-dual
root. -/
def klTermMassCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (klHeatExp V + 1) / (klHeatExp V + 1)) *
    basePowMass V (klQDual V)

/-- Hölder-dual root of the scalar terminal mass factor. -/
def klTermRoot (t : ℝ) : ℝ :=
  (klTermMassCore (V := V) t) ^ (1 / klQDual V)

/-- Dimension-only constant in the late ordinary-source heat estimate. -/
def klLate0C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  klTermRoot (V := V) 1

/-- The scalar terminal mass factor is positive at positive time. -/
theorem klTermCore_pos {t : ℝ} (ht : 0 < t) :
    0 < klTermMassCore (V := V) t := by
  have ha : 0 < klHeatExp V + 1 := by
    linarith [klHeatExp_gt (V := V)]
  unfold klTermMassCore
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos (half_pos ht) _) ha)
    (klBasePow_pos (V := V) (klQ_holder (V := V)).pos)

/-- Before taking the dual root, replacing `t` by `R^2` extracts the
`klLqScaleR R` factor to the power `klQDual`. -/
theorem klTermCore_scale {R : ℝ} (hR : 0 < R) :
    klTermMassCore (V := V) (R ^ 2) =
      (klLqScaleR (V := V) R) ^ klQDual V *
        klTermMassCore (V := V) 1 := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hexp :
      2 * (klHeatExp V + 1) =
        (4 / (Module.finrank ℝ V + 4 : ℝ)) * klQDual V := by
    have hdiv := klTermScale_exp (V := V)
    have hmul : klHeatExp V + 1 =
        (2 / (Module.finrank ℝ V + 4 : ℝ)) * klQDual V :=
      (div_eq_iff hp.ne').mp hdiv
    rw [hmul]
    ring
  have hscalePow :
      (klLqScaleR (V := V) R) ^ klQDual V =
        R ^ ((4 / (Module.finrank ℝ V + 4 : ℝ)) * klQDual V) := by
    simpa only [klLqScaleR, klDim] using
      (Real.rpow_mul hR.le
        (4 / (Module.finrank ℝ V + 4 : ℝ)) (klQDual V)).symm
  have hpow :
      (R ^ 2 / 2) ^ (klHeatExp V + 1) =
        (klLqScaleR (V := V) R) ^ klQDual V *
          ((1 : ℝ) / 2) ^ (klHeatExp V + 1) := by
    rw [show R ^ 2 / 2 = R ^ 2 * ((1 : ℝ) / 2) by ring]
    rw [Real.mul_rpow (sq_nonneg R) (by positivity)]
    rw [← Real.rpow_natCast_mul hR.le 2 (klHeatExp V + 1)]
    rw [hscalePow]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  unfold klTermMassCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

/-- Taking the Hölder-dual root turns the extracted power into exactly one
copy of the Koch--Lamm late-source scale. -/
theorem klTermRoot_scale {R : ℝ} (hR : 0 < R) :
    klTermRoot (V := V) (R ^ 2) =
      klLate0C V * klLqScaleR (V := V) R := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < klTermMassCore (V := V) 1 :=
    klTermCore_pos (V := V) one_pos
  have hpinv : klQDual V * (1 / klQDual V) = 1 := by
    field_simp [hp.ne']
  unfold klLate0C klTermRoot
  rw [klTermCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc.le]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

section Measured

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Exact global terminal kernel factor at observation time `R^2`. -/
theorem klTermNorm_scale {R : ℝ} (hR : 0 < R) (x : V) :
    (klTermPowMass (V := V) (R ^ 2) x) ^ (1 / klQDual V) =
      klLate0C V * klLqScaleR (V := V) R := by
  rw [klTermPowMass_eq (V := V) (sq_pos_of_pos hR) x]
  exact klTermRoot_scale (V := V) hR

end Measured

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
