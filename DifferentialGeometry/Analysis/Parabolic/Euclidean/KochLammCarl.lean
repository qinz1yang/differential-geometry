import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson

/-!
# Local energy from the Koch--Lamm `L²` arm

The local `L²` arm in the exact Koch--Lamm carrier is the square root of the
Carleson energy used by the nonlinear product estimates.  This file records
that identification and its scale cancellation for both fluxes and path
gradients.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [BorelSpace V] [NormedSpace ℝ G] in
/-- Squaring the `L²` seminorm gives the corresponding integral of the
squared norm. -/
theorem eLpNorm_two_sq (d : ℝ × V → G) (μ : Measure (ℝ × V)) :
    eLpNorm d 2 μ ^ 2 = ∫⁻ z, ENNReal.ofReal (‖d z‖ ^ 2) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  have hpow :
      (∫⁻ z, ‖d z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) =
        ∫⁻ z, ENNReal.ofReal (‖d z‖ ^ 2) ∂μ := by
    refine lintegral_congr ?_
    intro z
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num,
      ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [hpow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

omit [MeasurableSpace V] [BorelSpace V] in
/-- The inverse-square of the Koch--Lamm local `L²` scale is the spatial
volume scale `R^n`. -/
theorem klL2_inv_sq {R : ℝ} (hR : 0 < R) :
    (klL2Scale (V := V) R)⁻¹ ^ 2 =
      ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
  let a : ℝ := (Module.finrank ℝ V : ℝ) / 2
  have hneg :
      Real.rpow R (-a) = (Real.rpow R a)⁻¹ :=
    Real.rpow_neg hR.le _
  have hpos : 0 < Real.rpow R a := Real.rpow_pos_of_pos hR _
  have hof :
      ENNReal.ofReal ((Real.rpow R a)⁻¹) =
        (ENNReal.ofReal (Real.rpow R a))⁻¹ :=
    ENNReal.ofReal_inv_of_pos hpos
  rw [klL2Scale, klL2ScaleR, klDim]
  rw [show -((Module.finrank ℝ V : ℝ)) / 2 =
      -((Module.finrank ℝ V : ℝ) / 2) by ring]
  change
    (ENNReal.ofReal (Real.rpow R (-a)))⁻¹ ^ 2 =
      ENNReal.ofReal (R ^ Module.finrank ℝ V)
  rw [hneg, hof, inv_inv]
  have hpow :
      (ENNReal.ofReal (Real.rpow R a)) ^ 2 =
        ENNReal.ofReal ((Real.rpow R a) ^ 2) :=
    (ENNReal.ofReal_pow hpos.le 2).symm
  rw [hpow]
  congr 1
  calc
    (Real.rpow R a) ^ 2 = Real.rpow (Real.rpow R a) (2 : ℝ) :=
      (Real.rpow_natCast (Real.rpow R a) 2).symm
    _ = Real.rpow R (a * 2) := (Real.rpow_mul hR.le a 2).symm
    _ = Real.rpow R (Module.finrank ℝ V : ℝ) := by
      congr 1
      dsimp [a]
      ring
    _ = R ^ Module.finrank ℝ V :=
      Real.rpow_natCast R (Module.finrank ℝ V)

omit [NormedSpace ℝ G] in
/-- A Koch--Lamm divergence source has the local gradient-Carleson bound
with the square of its `L²` radius. -/
theorem kl1_to_gradCarl {T : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → G} (h : KLSource1 T A₂ Aₚ f) :
    GradCarl T ((A₂ : ℝ≥0∞) ^ 2) f := by
  refine ⟨?_, ?_⟩
  · simpa [klVolume, stVolume] using h.ae
  · intro x R hR hRT
    have hb := h.local_l2 x R hR hRT
    have hs0 : klL2Scale (V := V) R ≠ 0 :=
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hR (-klDim V / 2))).ne'
    have hsT : klL2Scale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
    have hi := (ENNReal.mul_le_iff_le_inv hs0 hsT).mp hb
    have hi' :
        eLpNorm f 2
            ((stVolume : Measure (ℝ × V)).restrict (paraCyl x R)) ≤
          (A₂ : ℝ≥0∞) * (klL2Scale (V := V) R)⁻¹ := by
      simpa [klVolume, stVolume, klCyl, paraCyl, mul_comm] using hi
    calc
      gradMass f x R =
          eLpNorm f 2
            ((stVolume : Measure (ℝ × V)).restrict (paraCyl x R)) ^ 2 := by
              rw [eLpNorm_two_sq]
              rfl
      _ ≤ ((A₂ : ℝ≥0∞) * (klL2Scale (V := V) R)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hi' 2
      _ = (A₂ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
        rw [mul_pow, klL2_inv_sq (V := V) hR]

omit [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- The local `L²` arm of a Koch--Lamm path gives the same gradient-Carleson
bound. -/
theorem klPath_gradCarl {T : ℝ} {A₀ A₂ Aₚ : ℝ≥0}
    {u : ℝ × V → F} {d : ℝ × V → G} (h : KLPath T A₀ A₂ Aₚ u d) :
    GradCarl T ((A₂ : ℝ≥0∞) ^ 2) d := by
  refine ⟨?_, ?_⟩
  · simpa [klVolume, stVolume] using h.grad_ae
  · intro x R hR hRT
    have hb := h.grad_l2 x R hR hRT
    have hs0 : klL2Scale (V := V) R ≠ 0 :=
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hR (-klDim V / 2))).ne'
    have hsT : klL2Scale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
    have hi := (ENNReal.mul_le_iff_le_inv hs0 hsT).mp hb
    have hi' :
        eLpNorm d 2
            ((stVolume : Measure (ℝ × V)).restrict (paraCyl x R)) ≤
          (A₂ : ℝ≥0∞) * (klL2Scale (V := V) R)⁻¹ := by
      simpa [klVolume, stVolume, klCyl, paraCyl, mul_comm] using hi
    calc
      gradMass d x R =
          eLpNorm d 2
            ((stVolume : Measure (ℝ × V)).restrict (paraCyl x R)) ^ 2 := by
              rw [eLpNorm_two_sq]
              rfl
      _ ≤ ((A₂ : ℝ≥0∞) * (klL2Scale (V := V) R)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hi' 2
      _ = (A₂ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
        rw [mul_pow, klL2_inv_sq (V := V) hR]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
