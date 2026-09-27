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

def kochLammCylinder (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc 0 (R ^ 2) ×ˢ Metric.ball x R

def kochLammLateCylinder (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc (R ^ 2 / 2) (R ^ 2) ×ˢ Metric.ball x R

def kochLammDim (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ :=
  Module.finrank ℝ V

def kochLammP (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ≥0∞ :=
  ((Module.finrank ℝ V + 4 : ℕ) : ℝ≥0∞)

def kochLammQ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    : ℝ≥0∞ :=
  kochLammP V / 2

omit [FiniteDimensional ℝ V] in
theorem kochLammP_ne_zero : kochLammP V ≠ 0 := by
  simp [kochLammP]

omit [FiniteDimensional ℝ V] in
theorem kochLammP_ne_top : kochLammP V ≠ ∞ := by
  simp [kochLammP]

omit [FiniteDimensional ℝ V] in
theorem kochLammQ_ne_zero : kochLammQ V ≠ 0 := by
  simp [kochLammQ, kochLammP]

omit [FiniteDimensional ℝ V] in
theorem kochLammQ_ne_top : kochLammQ V ≠ ∞ := by
  unfold kochLammQ
  exact ENNReal.div_ne_top (kochLammP_ne_top (V := V)) (by norm_num)

def kochLammL2ScaleR (R : ℝ) : ℝ :=
  R ^ (-kochLammDim V / 2)

def kochLammL2Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kochLammL2ScaleR (V := V) R)

def kochLammLpScaleR (R : ℝ) : ℝ :=
  R ^ (2 / (kochLammDim V + 4))

def kochLammLpScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kochLammLpScaleR (V := V) R)

def kochLammL1ScaleR (R : ℝ) : ℝ :=
  R ^ (-kochLammDim V)

def kochLammL1Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kochLammL1ScaleR (V := V) R)

def kochLammLqScaleR (R : ℝ) : ℝ :=
  R ^ (4 / (kochLammDim V + 4))

def kochLammLqScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (kochLammLqScaleR (V := V) R)

end Scaling

section MeasureSpaces

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def kochLammVolume : Measure (ℝ × V) :=
  (volume : Measure ℝ).prod (volume : Measure V)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure KochLammPath (T : ℝ) (A₀ A₂ Aₚ : ℝ≥0)
    (u : ℝ × V → F) (d : ℝ × V → G) : Prop where
  value : ∀ t x, 0 < t → t ≤ T → ‖u (t, x)‖ₑ ≤ (A₀ : ℝ≥0∞)
  grad_ae : AEStronglyMeasurable d (kochLammVolume : Measure (ℝ × V))
  grad_l2 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammL2Scale (V := V) R *
        eLpNorm d 2 ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R)) ≤
      (A₂ : ℝ≥0∞)
  grad_lp : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammLpScale (V := V) R *
        eLpNorm d (kochLammP V)
          ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
      (Aₚ : ℝ≥0∞)

structure KochLammSourceZero (T : ℝ) (A₁ A_q : ℝ≥0)
    (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (kochLammVolume : Measure (ℝ × V))
  local_l1 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammL1Scale (V := V) R *
        eLpNorm f 1 ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R)) ≤
      (A₁ : ℝ≥0∞)
  late_lq : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammLqScale (V := V) R *
        eLpNorm f (kochLammQ V)
          ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
      (A_q : ℝ≥0∞)

structure KochLammSourceOne (T : ℝ) (A₂ Aₚ : ℝ≥0)
    (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (kochLammVolume : Measure (ℝ × V))
  local_l2 : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammL2Scale (V := V) R *
        eLpNorm f 2 ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R)) ≤
      (A₂ : ℝ≥0∞)
  late_lp : ∀ x R, 0 < R → R ^ 2 ≤ T →
    kochLammLpScale (V := V) R *
        eLpNorm f (kochLammP V)
          ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
      (Aₚ : ℝ≥0∞)

structure KochLammSourceSplitting (T : ℝ) (A₁ A_q A₂ Aₚ : ℝ≥0)
    (f₀ : ℝ × V → F) (f₁ : ℝ × V → G) : Prop where
  source : KochLammSourceZero T A₁ A_q f₀
  flux : KochLammSourceOne T A₂ Aₚ f₁

end MeasureSpaces

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
