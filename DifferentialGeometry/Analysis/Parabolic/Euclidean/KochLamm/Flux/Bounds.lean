import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Near
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Scale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem kochLammFluxKernel_integral_rpow_le {R : ℝ} (hR : 0 < R) (w x : V) :
    (∫ z in kochLammLateCylinder x R,
        ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
          ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPDual V) ≤
      ‖w‖ * kochLammLate1C V * kochLammLpScaleR (V := V) R := by
  have hp : 0 < kochLammPDual V := (kochLammPDual_holder (V := V)).pos
  have hki : Integrable
      (fun z : ℝ × V ↦
        ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V)
      (kochLammTermMeasure (V := V) (R ^ 2)) := by
    have hm :=
      (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hmi : Integrable
      (fun z : ℝ × V ↦
        (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ kochLammPDual V)
      (kochLammTermMeasure (V := V) (R ^ 2)) := by
    have hm := ((kochLammFluxMajor_memLp (V := V) (t := R ^ 2) x).const_mul
      ‖w‖).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le,
      Real.norm_of_nonneg (norm_nonneg w),
      Real.norm_of_nonneg
        (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _), norm_mul] using hm
  have hlocal :
      (∫ z in kochLammLateCylinder x R,
          ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂(kochLammVolume : Measure (ℝ × V))) ≤
        ∫ z : ℝ × V,
          ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂(kochLammTermMeasure (V := V) (R ^ 2)) := by
    exact integral_mono_measure (kochLammLateMeasure_le (V := V) x R)
      (Filter.Eventually.of_forall fun z ↦
        Real.rpow_nonneg (norm_nonneg _) _)
      hki
  have hglobal :
      (∫ z : ℝ × V,
          ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂(kochLammTermMeasure (V := V) (R ^ 2))) ≤
        ∫ z : ℝ × V,
          (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ kochLammPDual V
            ∂(kochLammTermMeasure (V := V) (R ^ 2)) := by
    apply integral_mono_ae hki hmi
    filter_upwards [kochLammFluxKernel_ae (V := V) w x]
      with z hz
    exact Real.rpow_le_rpow (norm_nonneg _) hz hp.le
  have hmass :
      (∫ z : ℝ × V,
          (‖w‖ * kochLammFluxMajor (R ^ 2) x z) ^ kochLammPDual V
            ∂(kochLammTermMeasure (V := V) (R ^ 2))) =
        ‖w‖ ^ kochLammPDual V *
          kochLammFluxPowMass (V := V) (R ^ 2) x := by
    simp_rw [Real.mul_rpow (norm_nonneg w)
      (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _)]
    rw [integral_const_mul]
    unfold kochLammFluxPowMass
    simp_rw [Real.norm_of_nonneg
      (kochLammFluxMajor_nonneg (V := V) (R ^ 2) x _)]
  have hmono :
      (∫ z in kochLammLateCylinder x R,
          ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂(kochLammVolume : Measure (ℝ × V))) ≤
        ‖w‖ ^ kochLammPDual V * kochLammFluxPowMass (V := V) (R ^ 2) x := by
    rw [← hmass]
    exact hlocal.trans hglobal
  have hpinv : kochLammPDual V * (1 / kochLammPDual V) = 1 := by
    field_simp [hp.ne']
  have hfluxnn : 0 ≤ kochLammFluxPowMass (V := V) (R ^ 2) x := by
    unfold kochLammFluxPowMass
    exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    (∫ z in kochLammLateCylinder x R,
        ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
          ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPDual V) ≤
        (‖w‖ ^ kochLammPDual V *
          kochLammFluxPowMass (V := V) (R ^ 2) x) ^ (1 / kochLammPDual V) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hmono (by positivity)
    _ = ‖w‖ *
        (kochLammFluxPowMass (V := V) (R ^ 2) x) ^ (1 / kochLammPDual V) := by
      rw [Real.mul_rpow
        (Real.rpow_nonneg (norm_nonneg w) _)
        hfluxnn]
      rw [← Real.rpow_mul (norm_nonneg w), hpinv, Real.rpow_one]
    _ = ‖w‖ * (kochLammLate1C V * kochLammLpScaleR (V := V) R) := by
      rw [kochLammFluxNorm_scale (V := V) hR x]
    _ = ‖w‖ * kochLammLate1C V * kochLammLpScaleR (V := V) R := by ring

omit [Nontrivial V] [NormedSpace ℝ F] in
theorem kochLammFluxSource_integral_rpow_le {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammPReal V
        ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPReal V) ≤
      (kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ) := by
  let μ := (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)
  have hq : 0 < kochLammPReal V := (kochLammPDual_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxSource_memLp (V := V) h x hR hRT)
  have hfactor := realLpFactor_eq hq hf
  have hnorm := kochLammFluxSource_norm (V := V) h x hR hRT
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : kochLammLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (kochLammLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [kochLammPReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [kochLammLpScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

theorem kochLammFluxNear_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammFluxNear1 R w f x‖ ≤ ‖w‖ * kochLammLate1C V * (Aₚ : ℝ) := by
  have hk := kochLammFluxKernel_integral_rpow_le (V := V) hR w x
  have hf := kochLammFluxSource_integral_rpow_le (V := V) h x hR hRT
  have hh := kochLammFluxNear_holder (V := V) h w x hR hRT
  have hs : 0 < kochLammLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ kochLammLate1C V := by
    unfold kochLammLate1C kochLammFluxRoot
    exact Real.rpow_nonneg (kochLammFluxCore_nonneg (V := V) one_pos) _
  calc
    ‖kochLammFluxNear1 R w f x‖ ≤
        (∫ z in kochLammLateCylinder x R,
            ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
              ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPDual V) *
          (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammPReal V
              ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPReal V) := hh
    _ ≤ (‖w‖ * kochLammLate1C V * kochLammLpScaleR (V := V) R) *
          ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hk hf
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (mul_nonneg (norm_nonneg w) hc) hs.le)
    _ = ‖w‖ * kochLammLate1C V * (Aₚ : ℝ) := by
      calc
        (‖w‖ * kochLammLate1C V * kochLammLpScaleR (V := V) R) *
              ((kochLammLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * kochLammLate1C V *
              (kochLammLpScaleR (V := V) R *
                (kochLammLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * kochLammLate1C V * (Aₚ : ℝ) := by
          rw [mul_inv_cancel₀ hs.ne', mul_one]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
