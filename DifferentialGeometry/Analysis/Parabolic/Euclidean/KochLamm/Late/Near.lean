import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Schauder.HolderConvolution
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Kernel

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

omit [Nontrivial V] in
theorem kochLammLateMeasure_le (x : V) (R : ℝ) :
    (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R) ≤
      kochLammTermMeasure (V := V) (R ^ 2) := by
  unfold kochLammVolume kochLammLateCylinder kochLammTermMeasure
  rw [Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammLateSource_memLp {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    MemLp f (kochLammQ V)
      ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) := by
  refine ⟨h.ae.mono_measure Measure.restrict_le_self, ?_⟩
  have hb := h.late_lq x R hR hRT
  have hs0 : kochLammLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (4 / (kochLammDim V + 4)))).ne'
  have hmul : kochLammLqScale (V := V) R *
      eLpNorm f (kochLammQ V)
        ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) < ∞ :=
    lt_of_le_of_lt hb ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
theorem kochLammLateSource_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    eLpNorm f (kochLammQ V)
        ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
      (kochLammLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) := by
  have hs0 : kochLammLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (4 / (kochLammDim V + 4)))).ne'
  have hsT : kochLammLqScale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_iff_le_inv hs0 hsT).mp
    (h.late_lq x R hR hRT)

def kochLammLateNear0 (R : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in kochLammLateCylinder x R,
    kochLammTermKernel (R ^ 2) x z • f z ∂(kochLammVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
theorem kochLammLateNear_holder {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖kochLammLateNear0 R f x‖ ≤
      (∫ z in kochLammLateCylinder x R,
          ‖kochLammTermKernel (R ^ 2) x z‖ ^ kochLammQDual V
            ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQDual V) *
        (∫ z in kochLammLateCylinder x R, ‖f z‖ ^ kochLammQReal V
            ∂(kochLammVolume : Measure (ℝ × V))) ^ (1 / kochLammQReal V) := by
  let μ := (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)
  have hk : MemLp (kochLammTermKernel (R ^ 2) x)
      (ENNReal.ofReal (kochLammQDual V)) μ :=
    (kochLammTermKernel_memLp (V := V) (t := R ^ 2) x).mono_measure
      (kochLammLateMeasure_le (V := V) x R)
  have hf : MemLp f (ENNReal.ofReal (kochLammQReal V)) μ := by
    simpa only [kochLammQReal_ofReal] using
      (kochLammLateSource_memLp (V := V) h x hR hRT)
  simpa only [kochLammLateNear0, μ] using
    (integral_holder (kochLammQ_holder (V := V))
      (kochLammTermKernel (R ^ 2) x) f hk hf)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
