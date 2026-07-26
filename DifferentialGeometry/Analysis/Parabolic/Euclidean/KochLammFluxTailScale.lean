import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxScale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxTail

/-!
# Radius scaling of the terminal Koch--Lamm flux tail

The split-Gaussian tail mass has the same time exponent as the global flux
mass.  Taking the `klPDual` root therefore extracts exactly one
`klLpScaleR`, while the far factor becomes `exp (-k^2 / 8)`.
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
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- Scalar terminal flux-tail mass before taking the dual root. -/
def klFluxHalfCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1)) *
    baseD1HalfMass V (klPDual V)

/-- `klPDual` root of the split terminal flux-tail mass. -/
def klFluxHalfRoot (t : ℝ) : ℝ :=
  (klFluxHalfCore (V := V) t) ^ (1 / klPDual V)

/-- Dimension-only constant in the far late-flux estimate. -/
def klFluxTailC (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] : ℝ :=
  klFluxHalfRoot (V := V) 1

omit [Nontrivial V] in
/-- The split terminal flux mass is nonnegative at positive time. -/
theorem klFluxHalf_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ klFluxHalfCore (V := V) t := by
  have ha : 0 ≤ klD1Exp V + 1 := by
    linarith [klD1Exp_gt (V := V)]
  unfold klFluxHalfCore
  exact mul_nonneg
    (div_nonneg (Real.rpow_nonneg (half_pos ht).le _) ha)
    (baseD1HalfMass_nn (V := V) (klPDual V))

omit [Nontrivial V] in
/-- Replacing terminal time by `R^2` extracts the exact Koch--Lamm flux
radius scale to the `klPDual` power. -/
theorem klFluxHalf_scale {R : ℝ} (hR : 0 < R) :
    klFluxHalfCore (V := V) (R ^ 2) =
      (klLpScaleR (V := V) R) ^ klPDual V *
        klFluxHalfCore (V := V) 1 := by
  have hp : 0 < klPDual V := (klP_holder (V := V)).pos
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
  unfold klFluxHalfCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

omit [Nontrivial V] in
/-- Taking the dual root leaves exactly one copy of `klLpScaleR`. -/
theorem klFluxHRoot_scale {R : ℝ} (hR : 0 < R) :
    klFluxHalfRoot (V := V) (R ^ 2) =
      klFluxTailC V * klLpScaleR (V := V) R := by
  have hp : 0 < klPDual V := (klP_holder (V := V)).pos
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ klFluxHalfCore (V := V) 1 :=
    klFluxHalf_nonneg (V := V) one_pos
  have hpinv : klPDual V * (1 / klPDual V) = 1 := by
    field_simp [hp.ne']
  unfold klFluxTailC klFluxHalfRoot
  rw [klFluxHalf_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

/-- Every selected terminal flux-tail power mass is nonnegative. -/
theorem klFluxTailPow_nn (R : ℝ) (x : V) (S : Set V) :
    0 ≤ klFluxTailPow (V := V) R x S := by
  unfold klFluxTailPow
  exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- After taking the dual root, a `kR` far-field condition yields
`exp (-k^2/8)` and exactly one compensating `klLpScaleR`. -/
theorem klFluxTail_fac {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (klFluxTailPow (V := V) R x S) ^ (1 / klPDual V) ≤
      Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * klLpScaleR (V := V) R) := by
  let p : ℝ := klPDual V
  let E : ℝ := Real.exp (-(8 : ℝ)⁻¹ * k ^ 2)
  have hp : 0 < p := (klP_holder (V := V)).pos
  have hE : 0 < E := Real.exp_pos _
  have hcore : 0 ≤ klFluxHalfCore (V := V) (R ^ 2) :=
    klFluxHalf_nonneg (V := V) (sq_pos_of_pos hR)
  have htail : klFluxTailPow (V := V) R x S ≤
      E ^ p * klFluxHalfCore (V := V) (R ^ 2) := by
    simpa only [E, p, klFluxHalfCore] using
      (klFluxTail_pow (V := V) hR hk x hSm hfar)
  have hroot := Real.rpow_le_rpow
    (klFluxTailPow_nn (V := V) R x S) htail
    (by positivity : 0 ≤ 1 / p)
  have hpinv : p * (1 / p) = 1 := by
    field_simp [hp.ne']
  calc
    (klFluxTailPow (V := V) R x S) ^ (1 / klPDual V) =
        (klFluxTailPow (V := V) R x S) ^ (1 / p) := rfl
    _ ≤ (E ^ p * klFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) := hroot
    _ = E * (klFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hE.le p) hcore]
      rw [← Real.rpow_mul hE.le, hpinv, Real.rpow_one]
    _ = E * (klFluxTailC V * klLpScaleR (V := V) R) := by
      rw [show (klFluxHalfCore (V := V) (R ^ 2)) ^ (1 / p) =
          klFluxTailC V * klLpScaleR (V := V) R by
        simpa only [klFluxHalfRoot, p] using
          (klFluxHRoot_scale (V := V) hR)]
    _ = Real.exp (-(8 : ℝ)⁻¹ * k ^ 2) *
        (klFluxTailC V * klLpScaleR (V := V) R) := rfl

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
