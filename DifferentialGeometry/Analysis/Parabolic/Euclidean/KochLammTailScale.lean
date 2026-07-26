import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateScale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateTail

/-!
# Radius scaling of the terminal Koch--Lamm tail

This file takes the Hölder-dual root of the split-Gaussian tail mass.  The
terminal radius scale is the same as for the full kernel, while the extracted
Gaussian factor becomes `exp (-k^2 / 4)`.
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

/-- Scalar terminal tail mass before taking the Hölder-dual root. -/
def klTailCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (klHeatExp V + 1) / (klHeatExp V + 1)) *
    klTailMass V (klQDual V)

/-- Hölder-dual root of the scalar terminal tail mass. -/
def klTailRoot (t : ℝ) : ℝ :=
  (klTailCore (V := V) t) ^ (1 / klQDual V)

/-- Dimension-only constant in the late ordinary-source tail estimate. -/
def klLateTailC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  klTailRoot (V := V) 1

/-- The split-Gaussian mass is positive at every positive exponent. -/
theorem klTailMass_pos {p : ℝ} (hp : 0 < p) :
    0 < klTailMass V p := by
  unfold klTailMass
  exact mul_pos
    (Real.rpow_pos_of_pos (inv_pos.mpr (baseHeatMass_pos (V := V))) _)
    (klBasePow_pos (V := V) (half_pos hp))

/-- The scalar terminal tail mass is positive at positive time. -/
theorem klTailCore_pos {t : ℝ} (ht : 0 < t) :
    0 < klTailCore (V := V) t := by
  have ha : 0 < klHeatExp V + 1 := by
    linarith [klHeatExp_gt (V := V)]
  unfold klTailCore
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos (half_pos ht) _) ha)
    (klTailMass_pos (V := V) (klQ_holder (V := V)).pos)

/-- Replacing terminal time by `R^2` extracts the late-source radius scale
to the Hölder-dual power. -/
theorem klTailCore_scale {R : ℝ} (hR : 0 < R) :
    klTailCore (V := V) (R ^ 2) =
      (klLqScaleR (V := V) R) ^ klQDual V *
        klTailCore (V := V) 1 := by
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
  unfold klTailCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

/-- Taking the dual root leaves exactly one late-source radius scale. -/
theorem klTailRoot_scale {R : ℝ} (hR : 0 < R) :
    klTailRoot (V := V) (R ^ 2) =
      klLateTailC V * klLqScaleR (V := V) R := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < klTailCore (V := V) 1 :=
    klTailCore_pos (V := V) one_pos
  have hpinv : klQDual V * (1 / klQDual V) = 1 := by
    field_simp [hp.ne']
  unfold klLateTailC klTailRoot
  rw [klTailCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc.le]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

section Measured

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The kernel Hölder factor over a far terminal set has Gaussian decay and
the exact late-source radius scale. -/
theorem klTailKern_fac {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) ≤
      Real.exp (-(k ^ 2) / 4) *
        (klLateTailC V * klLqScaleR (V := V) R) := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hmass : 0 < klTailCore (V := V) (R ^ 2) :=
    klTailCore_pos (V := V) (sq_pos_of_pos hR)
  have hpow := klTermTail_pow (V := V) hR hk x hSm hfar
  change klTermTailPow (V := V) R x S ≤
    Real.exp (-(klQDual V * k ^ 2) / 4) *
      klTailCore (V := V) (R ^ 2) at hpow
  have hnonneg : 0 ≤ klTermTailPow (V := V) R x S := by
    unfold klTermTailPow
    exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    (klTermTailPow (V := V) R x S) ^ (1 / klQDual V) ≤
        (Real.exp (-(klQDual V * k ^ 2) / 4) *
          klTailCore (V := V) (R ^ 2)) ^ (1 / klQDual V) := by
      exact Real.rpow_le_rpow hnonneg hpow (by positivity)
    _ = Real.exp (-(k ^ 2) / 4) *
        klTailRoot (V := V) (R ^ 2) := by
      rw [Real.mul_rpow (Real.exp_pos _).le hmass.le]
      unfold klTailRoot
      congr 1
      rw [← Real.exp_mul]
      congr 1
      field_simp [hp.ne']
    _ = Real.exp (-(k ^ 2) / 4) *
        (klLateTailC V * klLqScaleR (V := V) R) := by
      rw [klTailRoot_scale (V := V) hR]

end Measured

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
