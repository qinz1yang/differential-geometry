import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Kernel

noncomputable section


open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def kochLammFluxMassCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (kochLammD1Exp V + 1) / (kochLammD1Exp V + 1)) *
    baseD1PowMass V (kochLammPDual V)

def kochLammFluxRoot (t : ℝ) : ℝ :=
  (kochLammFluxMassCore (V := V) t) ^ (1 / kochLammPDual V)

def kochLammLate1C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  kochLammFluxRoot (V := V) 1

theorem baseD1Pow_nonneg (p : ℝ) :
    0 ≤ baseD1PowMass V p := by
  unfold baseD1PowMass
  exact integral_nonneg fun x ↦ Real.rpow_nonneg (baseD1Maj_nonneg x) p

theorem kochLammFluxCore_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ kochLammFluxMassCore (V := V) t := by
  have ha : 0 ≤ kochLammD1Exp V + 1 := by
    linarith [kochLammD1Exp_gt (V := V)]
  unfold kochLammFluxMassCore
  exact mul_nonneg
    (div_nonneg (Real.rpow_nonneg (half_pos ht).le _) ha)
    (baseD1Pow_nonneg (V := V) (kochLammPDual V))

theorem kochLammFluxCore_scale {R : ℝ} (hR : 0 < R) :
    kochLammFluxMassCore (V := V) (R ^ 2) =
      (kochLammLpScaleR (V := V) R) ^ kochLammPDual V *
        kochLammFluxMassCore (V := V) 1 := by
  have hp : 0 < kochLammPDual V := (kochLammPDual_holder (V := V)).pos
  have hexp :
      2 * (kochLammD1Exp V + 1) =
        (2 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammPDual V := by
    have hdiv := kochLammD1Scale_exp (V := V)
    have hmul : kochLammD1Exp V + 1 =
        (1 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammPDual V :=
      (div_eq_iff hp.ne').mp hdiv
    rw [hmul]
    ring
  have hscalePow :
      (kochLammLpScaleR (V := V) R) ^ kochLammPDual V =
        R ^ ((2 / (Module.finrank ℝ V + 4 : ℝ)) * kochLammPDual V) := by
    simpa only [kochLammLpScaleR, kochLammDim] using
      (Real.rpow_mul hR.le
        (2 / (Module.finrank ℝ V + 4 : ℝ)) (kochLammPDual V)).symm
  have hpow :
      (R ^ 2 / 2) ^ (kochLammD1Exp V + 1) =
        (kochLammLpScaleR (V := V) R) ^ kochLammPDual V *
          ((1 : ℝ) / 2) ^ (kochLammD1Exp V + 1) := by
    rw [show R ^ 2 / 2 = R ^ 2 * ((1 : ℝ) / 2) by ring]
    rw [Real.mul_rpow (sq_nonneg R) (by positivity)]
    rw [← Real.rpow_natCast_mul hR.le 2 (kochLammD1Exp V + 1)]
    rw [hscalePow]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  unfold kochLammFluxMassCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

theorem kochLammFluxRoot_scale {R : ℝ} (hR : 0 < R) :
    kochLammFluxRoot (V := V) (R ^ 2) =
      kochLammLate1C V * kochLammLpScaleR (V := V) R := by
  have hp : 0 < kochLammPDual V := (kochLammPDual_holder (V := V)).pos
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ kochLammFluxMassCore (V := V) 1 :=
    kochLammFluxCore_nonneg (V := V) one_pos
  have hpinv : kochLammPDual V * (1 / kochLammPDual V) = 1 := by
    field_simp [hp.ne']
  unfold kochLammLate1C kochLammFluxRoot
  rw [kochLammFluxCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

variable [Nontrivial V] in
theorem kochLammFluxNorm_scale {R : ℝ} (hR : 0 < R) (x : V) :
    (kochLammFluxPowMass (V := V) (R ^ 2) x) ^ (1 / kochLammPDual V) =
      kochLammLate1C V * kochLammLpScaleR (V := V) R := by
  rw [kochLammFluxPowMass_eq (V := V) (sq_pos_of_pos hR) x]
  simpa only [kochLammFluxRoot, kochLammFluxMassCore] using
    (kochLammFluxRoot_scale (V := V) hR)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
