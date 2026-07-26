import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateNear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateScale
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative near late-source Koch--Lamm bound

This file converts the real power-integral factors in the joint space-time
Hölder estimate into `eLpNorm`s.  The exact terminal kernel scale then
cancels the inverse `KLSource0.late_lq` scale, giving a radius-independent
near-field bound.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Factor

variable {X F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup F]

/-- For a finite positive exponent, the real power-integral factor is the
real value of `eLpNorm`. -/
theorem realLpFactor_eq {μ : Measure X} {q : ℝ} (hq : 0 < q)
    {f : X → F} (hf : MemLp f (ENNReal.ofReal q) μ) :
    (∫ x, ‖f x‖ ^ q ∂μ) ^ (1 / q) =
      (eLpNorm f (ENNReal.ofReal q) μ).toReal := by
  have he := hf.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le] at he
  have hInt : 0 ≤ ∫ x, ‖f x‖ ^ q ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hfac : 0 ≤ (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ :=
    Real.rpow_nonneg hInt _
  apply_fun ENNReal.toReal at he
  rw [ENNReal.toReal_ofReal hfac] at he
  simpa only [one_div] using he.symm

end Factor

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The local terminal-cylinder kernel factor is bounded by the exact global
factor with its extracted Koch--Lamm radius scale. -/
theorem klLateKern_fac {R : ℝ} (hR : 0 < R) (x : V) :
    (∫ z in klLateCyl x R,
        ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
          ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQDual V) ≤
      klLate0C V * klLqScaleR (V := V) R := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V)
      (klTermMeasure (V := V) (R ^ 2)) := by
    have hm :=
      (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hmono :
      (∫ z in klLateCyl x R,
          ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
            ∂(klVolume : Measure (ℝ × V))) ≤
        klTermPowMass (V := V) (R ^ 2) x := by
    unfold klTermPowMass
    exact integral_mono_measure (klLateMeasure_le (V := V) x R)
      (Filter.Eventually.of_forall fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
      hi
  calc
    (∫ z in klLateCyl x R,
        ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
          ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQDual V) ≤
        (klTermPowMass (V := V) (R ^ 2) x) ^ (1 / klQDual V) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) hmono
        (by positivity)
    _ = klLate0C V * klLqScaleR (V := V) R :=
      klTermNorm_scale (V := V) hR x

omit [Nontrivial V] [NormedSpace ℝ F] in
/-- The late source power-integral factor has the inverse radius scale
advertised by `KLSource0.late_lq`. -/
theorem klLateSrc_fac {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    (∫ z in klLateCyl x R, ‖f z‖ ^ klQReal V
        ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQReal V) ≤
      (klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ) := by
  let μ := (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)
  have hq : 0 < klQReal V := (klQ_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klLateSrc_memLp (V := V) h x hR hRT)
  have hfactor := realLpFactor_eq hq hf
  have hnorm := klLateSrc_norm (V := V) h x hR hRT
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : klLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (klLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [klQReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [klLqScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

/-- Radius-independent near terminal-cylinder bound for an ordinary
Koch--Lamm source. -/
theorem klLateNear_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klLateNear0 R f x‖ ≤ klLate0C V * (A_q : ℝ) := by
  have hk := klLateKern_fac (V := V) hR x
  have hf := klLateSrc_fac (V := V) h x hR hRT
  have hh := klLateNear_holder (V := V) h x hR hRT
  have hs : 0 < klLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < klLate0C V := by
    unfold klLate0C klTermRoot
    exact Real.rpow_pos_of_pos (klTermCore_pos (V := V) one_pos) _
  calc
    ‖klLateNear0 R f x‖ ≤
        (∫ z in klLateCyl x R,
            ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
              ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQDual V) *
          (∫ z in klLateCyl x R, ‖f z‖ ^ klQReal V
              ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQReal V) := hh
    _ ≤ (klLate0C V * klLqScaleR (V := V) R) *
          ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hk hf
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg hc.le hs.le)
    _ = klLate0C V * (A_q : ℝ) := by
      calc
        (klLate0C V * klLqScaleR (V := V) R) *
              ((klLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            klLate0C V *
              (klLqScaleR (V := V) R *
                (klLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = klLate0C V * (A_q : ℝ) := by
          rw [mul_inv_cancel₀ hs.ne', mul_one]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
