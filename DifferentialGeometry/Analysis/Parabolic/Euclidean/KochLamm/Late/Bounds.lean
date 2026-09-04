import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Near
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Scale
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

theorem kochLammLateKernel_integral_rpow_le {R : ℝ} (hR : 0 < R) (x : V) :
    (∫ z in kochLammLateCylinder x R,
        ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V
          ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQDual V) ≤
      kochLammLate0C V * kochLammLqScaleR (V := V) R := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V)
      (kochLammTermMeasure (V := V) (R ^ 2)) := by
    have hm :=
      (kochLammTermKernel_memLp (V := V) (t := R ^ 2) x).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hmono :
      (∫ z in kochLammLateCylinder x R,
          ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V
            ∂(kochLammVolume : Measure (ℝ × V))) ≤
        kochLammTermPowMass (V := V) (R ^ 2) x := by
    unfold kochLammTermPowMass
    exact integral_mono_measure (kochLammLateMeasure_le (V := V) x R)
      (Filter.Eventually.of_forall fun z ↦ Real.rpow_nonneg (norm_nonneg _) _)
      hi
  calc
    (∫ z in kochLammLateCylinder x R,
        ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V
          ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQDual V) ≤
        (kochLammTermPowMass (V := V) (R ^ 2) x) ^ (1 / kochLammQDual V) := by
      exact Real.rpow_le_rpow
        (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) hmono
        (by positivity)
    _ = kochLammLate0C V * kochLammLqScaleR (V := V) R :=
      kochLammTermNorm_scale (V := V) hR x

omit [Nontrivial V] [NormedSpace ℝ F] in
theorem kochLammLateSource_integral_rpow_le {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammQReal V
        ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQReal V) ≤
      (kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ) := by
  let μ := (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)
  have hq : 0 < kochLammQReal V := (kochLammQ_holder (V := V)).symm.pos
  have hf : MemLp f (ENNReal.ofReal (kochLammQReal V)) μ := by
    simpa only [kochLammQReal_ofReal] using
      (kochLammLateSource_memLp (V := V) h x hR hRT)
  have hfactor := realLpFactor_eq hq hf
  have hnorm := kochLammLateSource_norm (V := V) h x hR hRT
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hs0 : kochLammLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have htop :
      (kochLammLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hs0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [kochLammQReal_ofReal] at hfactor
  rw [hfactor]
  simpa only [kochLammLqScale, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hs.le, ENNReal.coe_toReal] using hreal

theorem kochLammLateNear_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammLateNear0 R f x‖ ≤ kochLammLate0C V * (A_q : ℝ) := by
  have hk := kochLammLateKernel_integral_rpow_le (V := V) hR x
  have hf := kochLammLateSource_integral_rpow_le (V := V) h x hR hRT
  have hh := kochLammLateNear_holder (V := V) h x hR hRT
  have hs : 0 < kochLammLqScaleR (V := V) R :=
    Real.rpow_pos_of_pos hR _
  have hc : 0 < kochLammLate0C V := by
    unfold kochLammLate0C kochLammTermRoot
    exact Real.rpow_pos_of_pos (kochLammTermCore_pos (V := V) one_pos) _
  calc
    ‖kochLammLateNear0 R f x‖ ≤
        (∫ z in kochLammLateCylinder x R,
            ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V
              ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQDual V) *
          (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammQReal V
              ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQReal V) := hh
    _ ≤ (kochLammLate0C V * kochLammLqScaleR (V := V) R) *
          ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) :=
      mul_le_mul hk hf
        (Real.rpow_nonneg
          (integral_nonneg fun z ↦ Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg hc.le hs.le)
    _ = kochLammLate0C V * (A_q : ℝ) := by
      calc
        (kochLammLate0C V * kochLammLqScaleR (V := V) R) *
              ((kochLammLqScaleR (V := V) R)⁻¹ * (A_q : ℝ)) =
            kochLammLate0C V *
              (kochLammLqScaleR (V := V) R *
                (kochLammLqScaleR (V := V) R)⁻¹) * (A_q : ℝ) := by ring
        _ = kochLammLate0C V * (A_q : ℝ) := by
          rw [mul_inv_cancel₀ hs.ne', mul_one]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
