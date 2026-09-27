import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Schauder.HolderConvolution
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Kernel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Near

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
theorem kochLammFluxSource_memLp {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    MemLp f (kochLammP V)
      ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) := by
  refine ⟨h.ae.mono_measure Measure.restrict_le_self, ?_⟩
  have hb := h.late_lp x R hR hRT
  have hs0 : kochLammLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (2 / (kochLammDim V + 4)))).ne'
  have hmul : kochLammLpScale (V := V) R *
      eLpNorm f (kochLammP V)
        ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) < ∞ :=
    lt_of_le_of_lt hb ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammFluxSource_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    eLpNorm f (kochLammP V)
        ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
      (kochLammLpScale (V := V) R)⁻¹ * (Aₚ : ℝ≥0∞) := by
  have hs0 : kochLammLpScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (2 / (kochLammDim V + 4)))).ne'
  have hsT : kochLammLpScale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_iff_le_inv hs0 hsT).mp
    (h.late_lp x R hR hRT)

def kochLammFluxNear1 (R : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in kochLammLateCylinder x R,
    kochLammFluxKernel (R ^ 2) w x z • f z ∂(kochLammVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
theorem kochLammFluxNear_holder {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammFluxNear1 R w f x‖ ≤
      (∫ z in kochLammLateCylinder x R,
          ‖kochLammFluxKernel (R ^ 2) w x z‖ ^ kochLammPDual V
            ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPDual V) *
        (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammPReal V
            ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammPReal V) := by
  let μ := (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)
  have hk : MemLp (kochLammFluxKernel (R ^ 2) w x)
      (ENNReal.ofReal (kochLammPDual V)) μ :=
    (kochLammFluxKernel_memLp (V := V) (t := R ^ 2) w x).mono_measure
      (kochLammLateMeasure_le (V := V) x R)
  have hf : MemLp f (ENNReal.ofReal (kochLammPReal V)) μ := by
    simpa only [kochLammPReal_ofReal] using
      (kochLammFluxSource_memLp (V := V) h x hR hRT)
  simpa only [kochLammFluxNear1, μ] using
    (integral_holder (kochLammPDual_holder (V := V))
      (kochLammFluxKernel (R ^ 2) w x) f hk hf)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
