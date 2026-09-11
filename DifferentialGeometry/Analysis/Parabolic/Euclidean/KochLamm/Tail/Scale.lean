import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Scale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Tail

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def kochLammTailCore (t : ℝ) : ℝ :=
  ((t / 2) ^ (kochLammHeatExp V + 1) / (kochLammHeatExp V + 1)) *
    kochLammTailMass V (kochLammQDual V)

def kochLammTailRoot (t : ℝ) : ℝ :=
  (kochLammTailCore (V := V) t) ^ (1 / kochLammQDual V)

def kochLammLateTailC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [hFinite : FiniteDimensional ℝ V] : ℝ := by
  let _ := hFinite
  exact kochLammTailRoot (V := V) 1

omit [FiniteDimensional ℝ V] in
theorem kochLammTailMass_pos {p : ℝ} (hp : 0 < p) :
    0 < kochLammTailMass V p := by
  unfold kochLammTailMass
  exact mul_pos
    (Real.rpow_pos_of_pos (inv_pos.mpr (baseHeatMass_pos (V := V))) _)
    (kochLammBasePow_pos (V := V) (half_pos hp))

omit [FiniteDimensional ℝ V] in
theorem kochLammTailCore_pos {t : ℝ} (ht : 0 < t) :
    0 < kochLammTailCore (V := V) t := by
  have ha : 0 < kochLammHeatExp V + 1 := by
    linarith [kochLammHeatExp_gt (V := V)]
  unfold kochLammTailCore
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos (half_pos ht) _) ha)
    (kochLammTailMass_pos (V := V) (kochLammQ_holder (V := V)).pos)

omit [FiniteDimensional ℝ V] in
theorem kochLammTailCore_scale {R : ℝ} (hR : 0 < R) :
    kochLammTailCore (V := V) (R ^ 2) =
      (kochLammLqScaleR (V := V) R) ^ kochLammQDual V *
        kochLammTailCore (V := V) 1 := by
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
  unfold kochLammTailCore
  rw [hpow]
  norm_num only [one_div, one_pow]
  ring

theorem kochLammTailRoot_scale {R : ℝ} (hR : 0 < R) :
    kochLammTailRoot (V := V) (R ^ 2) =
      kochLammLateTailC V * kochLammLqScaleR (V := V) R := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < kochLammTailCore (V := V) 1 :=
    kochLammTailCore_pos (V := V) one_pos
  have hpinv : kochLammQDual V * (1 / kochLammQDual V) = 1 := by
    field_simp [hp.ne']
  unfold kochLammLateTailC kochLammTailRoot
  rw [kochLammTailCore_scale (V := V) hR]
  rw [Real.mul_rpow (Real.rpow_nonneg hs.le _) hc.le]
  rw [← Real.rpow_mul hs.le, hpinv, Real.rpow_one]
  ring

section Measured

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

theorem kochLammTailKernel_integral_rpow_le {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k)
    (x : V) {S : Set V} (hSm : MeasurableSet S)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) ≤
      Real.exp (-(k ^ 2) / 4) *
        (kochLammLateTailC V * kochLammLqScaleR (V := V) R) := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hmass : 0 < kochLammTailCore (V := V) (R ^ 2) :=
    kochLammTailCore_pos (V := V) (sq_pos_of_pos hR)
  have hpow := kochLammTermTail_pow (V := V) hR hk x hSm hfar
  change kochLammTermTailPow (V := V) R x S ≤
    Real.exp (-(kochLammQDual V * k ^ 2) / 4) *
      kochLammTailCore (V := V) (R ^ 2) at hpow
  have hnonneg : 0 ≤ kochLammTermTailPow (V := V) R x S := by
    unfold kochLammTermTailPow
    exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    (kochLammTermTailPow (V := V) R x S) ^ (1 / kochLammQDual V) ≤
        (Real.exp (-(kochLammQDual V * k ^ 2) / 4) *
          kochLammTailCore (V := V) (R ^ 2)) ^ (1 / kochLammQDual V) := by
      exact Real.rpow_le_rpow hnonneg hpow (by positivity)
    _ = Real.exp (-(k ^ 2) / 4) *
        kochLammTailRoot (V := V) (R ^ 2) := by
      rw [Real.mul_rpow (Real.exp_pos _).le hmass.le]
      unfold kochLammTailRoot
      congr 1
      rw [← Real.exp_mul]
      congr 1
      field_simp [hp.ne']
    _ = Real.exp (-(k ^ 2) / 4) *
        (kochLammLateTailC V * kochLammLqScaleR (V := V) R) := by
      rw [kochLammTailRoot_scale (V := V) hR]

end Measured

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
