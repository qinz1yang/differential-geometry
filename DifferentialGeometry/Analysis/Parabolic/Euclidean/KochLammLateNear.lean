import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelHolder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateKern

/-!
# Near terminal-cylinder Koch--Lamm estimate

The late ordinary-source estimate is a genuinely space-time Hölder estimate.
This file restricts the terminal heat-kernel class to one Koch--Lamm late
cylinder and pairs it with the matching `KLSource0.late_lq` arm.  In
particular, no uniform-in-time spatial `L^q` bound is extracted from the
source hypothesis.
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

omit [Nontrivial V] in
/-- A Koch--Lamm late cylinder is contained, as a restricted product
measure, in the corresponding full-space terminal slab. -/
theorem klLateMeasure_le (x : V) (R : ℝ) :
    (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R) ≤
      klTermMeasure (V := V) (R ^ 2) := by
  unfold klVolume klLateCyl klTermMeasure
  rw [Measure.restrict_prod_eq_prod_univ]
  exact Measure.restrict_mono
    (Set.prod_mono (subset_refl _) (Set.subset_univ _)) le_rfl

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The finite late-cylinder source estimate supplies the local `MemLp`
fact needed for space-time Hölder. -/
theorem klLateSrc_memLp {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    MemLp f (klQ V)
      ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) := by
  refine ⟨h.ae.mono_measure Measure.restrict_le_self, ?_⟩
  have hb := h.late_lq x R hR hRT
  have hs0 : klLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (4 / (klDim V + 4)))).ne'
  have hmul : klLqScale (V := V) R *
      eLpNorm f (klQ V)
        ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) < ∞ :=
    lt_of_le_of_lt hb ENNReal.coe_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hmul.ne hs0

omit [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Quantitative form of the same late-cylinder source estimate, with the
positive Koch--Lamm scale divided out. -/
theorem klLateSrc_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    eLpNorm f (klQ V)
        ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
      (klLqScale (V := V) R)⁻¹ * (A_q : ℝ≥0∞) := by
  have hs0 : klLqScale (V := V) R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hR (4 / (klDim V + 4)))).ne'
  have hsT : klLqScale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_iff_le_inv hs0 hsT).mp
    (h.late_lq x R hR hRT)

/-- The contribution of one late Koch--Lamm cylinder to the terminal-time
ordinary heat potential. -/
def klLateNear0 (R : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ z in klLateCyl x R,
    klTermKernel (R ^ 2) x z • f z ∂(klVolume : Measure (ℝ × V))

omit [CompleteSpace F] in
/-- Space-time Hölder controls the near terminal-cylinder heat potential in
the exact conjugate exponents. -/
theorem klLateNear_holder {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) :
    ‖klLateNear0 R f x‖ ≤
      (∫ z in klLateCyl x R,
          ‖klTermKernel (R ^ 2) x z‖ ^ klQDual V
            ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQDual V) *
        (∫ z in klLateCyl x R, ‖f z‖ ^ klQReal V
            ∂(klVolume : Measure (ℝ × V))) ^ (1 / klQReal V) := by
  let μ := (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)
  have hk : MemLp (klTermKernel (R ^ 2) x)
      (ENNReal.ofReal (klQDual V)) μ :=
    (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).mono_measure
      (klLateMeasure_le (V := V) x R)
  have hf : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klLateSrc_memLp (V := V) h x hR hRT)
  simpa only [klLateNear0, μ] using
    (integral_holder (klQ_holder (V := V))
      (klTermKernel (R ^ 2) x) f hk hf)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
