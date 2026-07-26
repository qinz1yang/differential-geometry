import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelHolder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxKern
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateNear

/-!
# Near terminal-cylinder Koch--Lamm flux estimate

This file restricts the full terminal first-derivative kernel class to one
late Koch--Lamm cylinder and pairs it with `KLSource1.late_lp`.  The estimate
is genuinely space-time Hölder; it does not extract an unavailable
uniform-in-time spatial source norm.
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
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The finite late-cylinder flux estimate supplies the local `MemLp` fact
needed for space-time Hölder. -/
theorem klFluxSrc_memLp {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    MemLp f (klP V)
      ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) := by
  refine ⟨h.ae.mono_measure Measure.restrict_le_self, ?_⟩
  have hb := h.late_lp x R hR hRT
  have hs0 : klLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (2 / (klDim V + 4)))).ne'
  have hmul : klLpScale (V := V) R *
      eLpNorm f (klP V)
        ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) < ∞ :=
    lt_of_le_of_lt hb ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Quantitative late-cylinder flux estimate, with the positive
Koch--Lamm scale divided out. -/
theorem klFluxSrc_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    eLpNorm f (klP V)
        ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
      (klLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) := by
  have hs0 : klLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (2 / (klDim V + 4)))).ne'
  have hsT : klLpScale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_iff_le_inv hs0 hsT).mp
    (h.late_lp x R hR hRT)

/-- Contribution of one late Koch--Lamm cylinder to a directional
divergence-source heat potential. -/
def klFluxNear1 (R : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in klLateCyl x R,
    klFluxKernel (R ^ 2) w x z • f z ∂(klVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
/-- Space-time Hölder controls the near terminal-cylinder directional
flux potential in the exact conjugate exponents. -/
theorem klFluxNear_holder {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klFluxNear1 R w f x‖ ≤
      (∫ z in klLateCyl x R,
          ‖klFluxKernel (R ^ 2) w x z‖ ^ klPDual V
            ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPDual V) *
        (∫ z in klLateCyl x R, ‖f z‖ ^ klPReal V
            ∂(klVolume : Measure (ℝ × V))) ^ (1 / klPReal V) := by
  let μ := (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)
  have hk : MemLp (klFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (klPDual V)) μ :=
    (klFluxKernel_memLp (V := V) (sq_pos_of_pos hR) w x).mono_measure
      (klLateMeasure_le (V := V) x R)
  have hf : MemLp f (ENNReal.ofReal (klPReal V)) μ := by
    simpa only [klPReal_ofReal] using
      (klFluxSrc_memLp (V := V) h x hR hRT)
  simpa only [klFluxNear1, μ] using
    (integral_holder (klP_holder (V := V))
      (klFluxKernel (R ^ 2) w x) f hk hf)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
