import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxKern

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

def klFluxMassCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1)) *
    baseD1PowMass V (klPDual V)

def klFluxRoot (t : ℝ) : ℝ :=
  (klFluxMassCore (V := V) t) ^ (1 / klPDual V)

def klLate1C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  klFluxRoot (V := V) 1

theorem baseD1Pow_nonneg (p : ℝ) :
    0 ≤ baseD1PowMass V p := by
  unfold baseD1PowMass
  exact integral_nonneg fun x ↦ Real.rpow_nonneg (baseD1Maj_nonneg x) p

theorem klFluxCore_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ klFluxMassCore (V := V) t := by
  have ha : 0 ≤ klD1Exp V + 1 := by
    linarith [klD1Exp_gt (V := V)]
  unfold klFluxMassCore
  exact mul_nonneg
    (div_nonneg (Real.rpow_nonneg (half_pos ht).le _) ha)
    (baseD1Pow_nonneg (V := V) (klPDual V))

theorem klFluxCore_scale {R : ℝ} (hR : 0 < R) :
    klFluxMassCore (V := V) (R ^ 2) =
      (klLpScaleR (V := V) R) ^ klPDual V *
        klFluxMassCore (V := V) 1 := by
  have hp : 0 < klPDual V := (klPDual_holder (V := V)).pos
  have hexp :
      2 * (klD1Exp V + 1) =
        (2 / (Module.finrank ℝ V + 4 : ℝ)) * klPDual V := by
    have hdiv := klD1Scale_exp (V := V)
    have hmul : klD1Exp V + 1 =
        (1 / (Module.finrank ℝ V + 4 : ℝ)) * klPDual V :=
      (div_eq_iff hp.ne').mp hdiv
    rw [hmul]
    ring
  have hscalePow :
      (klLpScaleR (V := V) R) ^ klPDual V =
        R ^ ((2 / (Module.finrank ℝ V + 4 : ℝ)) * klPDual V) := by
    simpa only [klLpScaleR, klDim] using
      (Real.rpow_mul hR.le
        (2 / (Module.finrank ℝ V + 4 : ℝ)) (klPDual V)).symm
  have hpow :
      (R ^ 2 / 2) ^ (klD1Exp V + 1) =
        (klLpScaleR (V := V) R) ^ klPDual V *
          ((1 : ℝ) / 2) ^ (klD1Exp V + 1) := by
    rw [show R ^ 2 / 2 = R ^ 2 * ((1 : ℝ) / 2) by ring]
    rw [Real.mul_rpow (sq_nonneg R) (by positivity)]
    rw [← Real.rpow_natCast_mul hR.le 2 (klD1Exp V + 1)]
    rw [hscalePow]
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  unfold klFluxMassCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

theorem klFluxRoot_scale {R : ℝ} (hR : 0 < R) :
    klFluxRoot (V := V) (R ^ 2) =
      klLate1C V * klLpScaleR (V := V) R := by
  have hp : 0 < klPDual V := (klPDual_holder (V := V)).pos
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ klFluxMassCore (V := V) 1 :=
    klFluxCore_nonneg (V := V) one_pos
  have hpinv : klPDual V * (1 / klPDual V) = 1 := by
    field_simp [hp.ne']
  unfold klLate1C klFluxRoot
  rw [klFluxCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

variable [Nontrivial V] in
theorem klFluxNorm_scale {R : ℝ} (hR : 0 < R) (x : V) :
    (klFluxPowMass (V := V) (R ^ 2) x) ^ (1 / klPDual V) =
      klLate1C V * klLpScaleR (V := V) R := by
  rw [klFluxPowMass_eq (V := V) (sq_pos_of_pos hR) x]
  simpa only [klFluxRoot, klFluxMassCore] using
    (klFluxRoot_scale (V := V) hR)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
