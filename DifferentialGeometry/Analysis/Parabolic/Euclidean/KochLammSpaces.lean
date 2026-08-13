import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Scaling

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def klCyl (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc 0 (R ^ 2) ×ˢ Metric.ball x R

def klLateCyl (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc (R ^ 2 / 2) (R ^ 2) ×ˢ Metric.ball x R

def klDim (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  Module.finrank ℝ V

def klP (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  ((Module.finrank ℝ V + 4 : ℕ) : ℝ≥0∞)

def klQ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  klP V / 2

theorem klP_ne_zero : klP V ≠ 0 := by
  simp [klP]

theorem klP_ne_top : klP V ≠ ∞ := by
  simp [klP]

theorem klQ_ne_zero : klQ V ≠ 0 := by
  simp [klQ, klP]

theorem klQ_ne_top : klQ V ≠ ∞ := by
  unfold klQ
  exact ENNReal.div_ne_top (klP_ne_top (V := V)) (by norm_num)

def klL2ScaleR (R : ℝ) : ℝ :=
  Real.rpow R (-klDim V / 2)

def klL2Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klL2ScaleR (V := V) R)

def klLpScaleR (R : ℝ) : ℝ :=
  Real.rpow R (2 / (klDim V + 4))

def klLpScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klLpScaleR (V := V) R)

def klL1ScaleR (R : ℝ) : ℝ :=
  Real.rpow R (-klDim V)

def klL1Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klL1ScaleR (V := V) R)

def klLqScaleR (R : ℝ) : ℝ :=
  Real.rpow R (4 / (klDim V + 4))

def klLqScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klLqScaleR (V := V) R)

end Scaling

section MeasureSpaces

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def klVolume : Measure (ℝ × V) :=
  (volume : Measure ℝ).prod (volume : Measure V)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure KLPath (T : ℝ) (A₀ A₂ Aₚ : ℝ≥0)
    (u : ℝ × V → F) (d : ℝ × V → G) : Prop where
  value : ∀ t x, 0 < t → t ≤ T → ‖u (t, x)‖ₑ ≤ (A₀ : ℝ≥0∞)
  grad_ae : AEStronglyMeasurable d (klVolume : Measure (ℝ × V))
  grad_l2 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klL2Scale (V := V) R *
        eLpNorm d 2 ((klVolume : Measure (ℝ × V)).restrict (klCyl x R)) ≤
      (A₂ : ℝ≥0∞)
  grad_lp : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klLpScale (V := V) R *
        eLpNorm d (klP V)
          ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
      (Aₚ : ℝ≥0∞)

structure KLSource0 (T : ℝ) (A₁ A_q : ℝ≥0)
    (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (klVolume : Measure (ℝ × V))
  local_l1 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klL1Scale (V := V) R *
        eLpNorm f 1 ((klVolume : Measure (ℝ × V)).restrict (klCyl x R)) ≤
      (A₁ : ℝ≥0∞)
  late_lq : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klLqScale (V := V) R *
        eLpNorm f (klQ V)
          ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
      (A_q : ℝ≥0∞)

structure KLSource1 (T : ℝ) (A₂ Aₚ : ℝ≥0)
    (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (klVolume : Measure (ℝ × V))
  local_l2 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klL2Scale (V := V) R *
        eLpNorm f 2 ((klVolume : Measure (ℝ × V)).restrict (klCyl x R)) ≤
      (A₂ : ℝ≥0∞)
  late_lp : ∀ x R, 0 < R → R ^ 2 ≤ T →
    klLpScale (V := V) R *
        eLpNorm f (klP V)
          ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
      (Aₚ : ℝ≥0∞)

structure KLSplit (T : ℝ) (A₁ A_q A₂ Aₚ : ℝ≥0)
    (f₀ : ℝ × V → F) (f₁ : ℝ × V → G) : Prop where
  source : KLSource0 T A₁ A_q f₀
  flux : KLSource1 T A₂ Aₚ f₁

end MeasureSpaces

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
