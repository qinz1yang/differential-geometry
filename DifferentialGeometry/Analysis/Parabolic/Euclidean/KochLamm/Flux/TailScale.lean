import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Scale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Tail

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def kochLammFluxHalfCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (kochLammD1Exp V + 1) / (kochLammD1Exp V + 1)) *
    baseD1HalfMass V (kochLammPDual V)

def kochLammFluxHalfRoot (t : ℝ) : ℝ :=
  (kochLammFluxHalfCore (V := V) t) ^ (1 / kochLammPDual V)

def kochLammFluxTailC (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] : ℝ :=
  kochLammFluxHalfRoot (V := V) 1

omit [Nontrivial V] in
theorem kochLammFluxHalf_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ kochLammFluxHalfCore (V := V) t := by
  have ha : 0 ≤ kochLammD1Exp V + 1 := by
    linarith [kochLammD1Exp_gt (V := V)]
  unfold kochLammFluxHalfCore
  exact mul_nonneg
    (div_nonneg (Real.rpow_nonneg (half_pos ht).le _) ha)
    (baseD1HalfMass_nn (V := V) (kochLammPDual V))

omit [Nontrivial V] in
theorem kochLammFluxHalf_scale {R : ℝ} (hR : 0 < R) :
    kochLammFluxHalfCore (V := V) (R ^ 2) =
      (kochLammLpScaleR (V := V) R) ^ kochLammPDual V *
        kochLammFluxHalfCore (V := V) 1 := by
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
  unfold kochLammFluxHalfCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

omit [Nontrivial V] in
theorem kochLammFluxHRoot_scale {R : ℝ} (hR : 0 < R) :
    kochLammFluxHalfRoot (V := V) (R ^ 2) =
      kochLammFluxTailC V * kochLammLpScaleR (V := V) R := by
  have hp : 0 < kochLammPDual V := (kochLammPDual_holder (V := V)).pos
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ kochLammFluxHalfCore (V := V) 1 :=
    kochLammFluxHalf_nonneg (V := V) one_pos
  have hpinv : kochLammPDual V * (1 / kochLammPDual V) = 1 := by
    field_simp [hp.ne']
  unfold kochLammFluxTailC kochLammFluxHalfRoot
  rw [kochLammFluxHalf_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

omit [Nontrivial V] in
theorem kochLammFluxTailPow_nn (R : ℝ) (x : V) (S : Set V) :
    0 ≤ kochLammFluxTailPow (V := V) R x S := by
  unfold kochLammFluxTailPow
  exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem kochLammFluxTail_integral_rpow_le {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (kochLammFluxTailPow (V := V) R x S) ^ (1 / kochLammPDual V) ≤
      Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * kochLammLpScaleR (V := V) R) := by
  let p : ℝ := kochLammPDual V
  let E : ℝ := Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)
  have hp : 0 < p := (kochLammPDual_holder (V := V)).pos
  have hE : 0 < E := Real.exp_pos _
  have hcore : 0 ≤ kochLammFluxHalfCore (V := V) (R ^ 2) :=
    kochLammFluxHalf_nonneg (V := V) (sq_pos_of_pos hR)
  have htail : kochLammFluxTailPow (V := V) R x S ≤
      E ^ p * kochLammFluxHalfCore (V := V) (R ^ 2) := by
    simpa only [E, p, kochLammFluxHalfCore] using
      (kochLammFluxTail_pow (V := V) hR hk x hSm hfar)
  have hroot := Real.rpow_le_rpow
    (kochLammFluxTailPow_nn (V := V) R x S) htail
    (by positivity : 0 ≤ 1 / p)
  have hpinv : p * (1 / p) = 1 := by
    field_simp [hp.ne']
  calc
    (kochLammFluxTailPow (V := V) R x S) ^ (1 / kochLammPDual V) =
        (kochLammFluxTailPow (V := V) R x S) ^ (1 / p) := rfl
    _ ≤ (E ^ p * kochLammFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) := hroot
    _ = E * (kochLammFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hE.le p) hcore]
      rw [← Real.rpow_mul hE.le, hpinv, Real.rpow_one]
    _ = E * (kochLammFluxTailC V * kochLammLpScaleR (V := V) R) := by
      rw [show (kochLammFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) =
          kochLammFluxTailC V * kochLammLpScaleR (V := V) R by
        simpa only [kochLammFluxHalfRoot, p] using
          (kochLammFluxHRoot_scale (V := V) hR)]
    _ = Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (kochLammFluxTailC V * kochLammLpScaleR (V := V) R) := rfl

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
