import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxNear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxScale
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative near late-flux Koch--Lamm bound

The directional first-derivative kernel is dominated by its radial
majorant.  Its exact terminal-slab scale cancels the inverse scale in
`KLSource1.late_lp`, yielding a radius-independent bound on one late
cylinder.
-/

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

/-- The local directional terminal-kernel factor is bounded by the global
radial factor, including the norm of the chosen direction. -/
theorem klFluxKern_fac {R : ℝ} (hR : 0 < R) (w x : V) :
    (∫ z in klLateCyl x R,
        ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
          ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPDual V) ≤
      ‖w‖ * klLate1C V * klLpScaleR (V := V) R := by
  have hp : 0 < klPDual V := (klP_holder (V := V)).pos
  have hki : Integrable
      (fun z : ℝ × V ↦
        ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V)
      (klTermMeasure (V := V) (R ^ 2)) := by
    have hm :=
      (klFluxKernel_memLp (V := V) (sq_pos_of_pos hR) w x).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hmi : Integrable
      (fun z : ℝ × V ↦
        (‖w‖ * klFluxMajor (R ^ 2) x z) ^ klPDual V)
      (klTermMeasure (V := V) (R ^ 2)) := by
    have hm := ((klFluxMajor_memLp (V := V) (sq_pos_of_pos hR) x).const_mul
      ‖w‖).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le,
      Real.norm_of_nonneg (norm_nonneg w),
      Real.norm_of_nonneg
        (klFluxMajor_nonneg (V := V) (R ^ 2) x _), norm_mul] using hm
  have hlocal :
      (∫ z in klLateCyl x R,
          ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂(klVolume : Measure (ℝ × V))) ≤
        ∫ z : ℝ × V,
          ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂(klTermMeasure (V := V) (R ^ 2)) := by
    exact integral_mono_measure (klLateMeasure_le (V := V) x R)
      (Filter.Eventually.of_forall fun z ↦
        Real.rpow_nonneg (norm_nonneg _) _)
      hki
  have hglobal :
      (∫ z : ℝ × V,
          ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂(klTermMeasure (V := V) (R ^ 2))) ≤
        ∫ z : ℝ × V,
          (‖w‖ * klFluxMajor (R ^ 2) x z) ^ klPDual V
            ∂(klTermMeasure (V := V) (R ^ 2)) := by
    apply integral_mono_ae hki hmi
    filter_upwards [klFluxKernel_ae (V := V) (sq_pos_of_pos hR) w x]
      with z hz
    exact Real.rpow_le_rpow (norm_nonneg _) hz hp.le
  have hmass :
      (∫ z : ℝ × V,
          (‖w‖ * klFluxMajor (R ^ 2) x z) ^ klPDual V
            ∂(klTermMeasure (V := V) (R ^ 2))) =
        ‖w‖ ^ klPDual V *
          klFluxPowMass (V := V) (R ^ 2) x := by
    simp_rw [Real.mul_rpow (norm_nonneg w)
      (klFluxMajor_nonneg (V := V) (R ^ 2) x _)]
    rw [integral_const_mul]
    unfold klFluxPowMass
    simp_rw [Real.norm_of_nonneg
      (klFluxMajor_nonneg (V := V) (R ^ 2) x _)]
  have hmono :
      (∫ z in klLateCyl x R,
          ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂(klVolume : Measure (ℝ × V))) ≤
        ‖w‖ ^ klPDual V * klFluxPowMass (V := V) (R ^ 2) x := by
    rw [← hmass]
    exact hlocal.trans hglobal
  have hpinv : klPDual V * (1 / klPDual V) = 1 := by
    field_simp [hp.ne']
  have hfluxnn : 0 ≤ klFluxPowMass (V := V) (R ^ 2) x := by
    unfold klFluxPowMass
    exact integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    (∫ z in klLateCyl x R,
        ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
          ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPDual V) ≤
        (‖w‖ ^ klPDual V *
          klFluxPowMass (V := V) (R ^ 2) x) ^ (1 / klPDual V) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
        hmono (by positivity)
    _ = ‖w‖ *
        (klFluxPowMass (V := V) (R ^ 2) x) ^ (1 / klPDual V) := by
      rw [Real.mul_rpow
        (Real.rpow_nonneg (norm_nonneg w) _)
        hfluxnn]
      rw [← Real.rpow_mul (norm_nonneg w), hpinv, Real.rpow_one]
    _ = ‖w‖ * (klLate1C V * klLpScaleR (V := V) R) := by
      rw [klFluxNorm_scale (V := V) hR x]
    _ = ‖w‖ * klLate1C V * klLpScaleR (V := V) R := by ring

omit [Nontrivial V] [NormedSpace ℝ F] in
/-- The late flux-source power-integral factor has the inverse radius scale
advertised by `KLSource1.late_lp`. -/
theorem klFluxSrc_fac {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    (∫ z in klLateCyl x R, ‖f z‖ ^ klPReal V
        ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPReal V) ≤
      (klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ) := by
  let μ := (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)
  have hq : 0 < klPReal V := (klP_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (klPReal V)) μ := by
    simpa only [klPReal_ofReal] using
      (klFluxSrc_memLp (V := V) h x hR hRT)
  have hfactor := realLpFactor_eq hq hf
  have hnorm := klFluxSrc_norm (V := V) h x hR hRT
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : klLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (klLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [klPReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [klLpScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

/-- Radius-independent near terminal-cylinder bound for one directional
component of a divergence-form Koch--Lamm source. -/
theorem klFluxNear_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klFluxNear1 R w f x‖ ≤ ‖w‖ * klLate1C V * (Aₚ : ℝ) := by
  have hk := klFluxKern_fac (V := V) hR w x
  have hf := klFluxSrc_fac (V := V) h x hR hRT
  have hh := klFluxNear_holder (V := V) h w x hR hRT
  have hs : 0 < klLpScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 ≤ klLate1C V := by
    unfold klLate1C klFluxRoot
    exact Real.rpow_nonneg (klFluxCore_nonneg (V := V) one_pos) _
  calc
    ‖klFluxNear1 R w f x‖ ≤
        (∫ z in klLateCyl x R,
            ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
              ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPDual V) *
          (∫ z in klLateCyl x R, ‖f z‖ ^ klPReal V
              ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPReal V) := hh
    _ ≤ (‖w‖ * klLate1C V * klLpScaleR (V := V) R) *
          ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) :=
      mul_le_mul hk hf
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg (mul_nonneg (norm_nonneg w) hc) hs.le)
    _ = ‖w‖ * klLate1C V * (Aₚ : ℝ) := by
      calc
        (‖w‖ * klLate1C V * klLpScaleR (V := V) R) *
              ((klLpScaleR (V := V) R)⁻¹ * (Aₚ : ℝ)) =
            ‖w‖ * klLate1C V *
              (klLpScaleR (V := V) R *
                (klLpScaleR (V := V) R)⁻¹) * (Aₚ : ℝ) := by ring
        _ = ‖w‖ * klLate1C V * (Aₚ : ℝ) := by
          rw [mul_inv_cancel₀ hs.ne', mul_one]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
