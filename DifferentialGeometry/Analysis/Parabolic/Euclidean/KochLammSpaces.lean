import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Koch--Lamm Ricci--DeTurck spaces

This file records the scale-invariant spaces used in Section 4 of
Koch--Lamm, *Geometric flows with rough initial data*.  The solution space is
not a weighted pointwise-gradient space.  Its three arms are

* a space-time `L∞` value bound;
* a local cylinder `L²` bound for the spatial gradient down to the initial
  edge;
* a local `L^(n+4)` gradient bound on the late half of each cylinder.

The source is split as `f₀ + div f₁`.  The ordinary source uses local `L¹`
and late `L^((n+4)/2)` control; the flux uses the same local `L²` and late
`L^(n+4)` controls as a gradient.

Only the exact predicates and scaling factors are introduced here.  Their
complete carriers and the concrete heat-potential estimates are separate
producers.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Product Lebesgue measure on Euclidean space-time. -/
def klVolume : Measure (ℝ × V) :=
  (volume : Measure ℝ).prod (volume : Measure V)

/-- The forward parabolic cylinder `(0,R²] × B(x,R)`. -/
def klCyl (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc 0 (R ^ 2) ×ˢ Metric.ball x R

/-- The late half-cylinder `(R²/2,R²] × B(x,R)`. -/
def klLateCyl (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc (R ^ 2 / 2) (R ^ 2) ×ˢ Metric.ball x R

/-- The dimension, viewed as a real scaling exponent. -/
def klDim (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  Module.finrank ℝ V

/-- Koch--Lamm's supercritical exponent `p = n + 4`. -/
def klP (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  ((Module.finrank ℝ V + 4 : ℕ) : ℝ≥0∞)

/-- The ordinary-source late exponent `q = (n+4)/2`. -/
def klQ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ≥0∞ :=
  klP V / 2

omit [MeasurableSpace V] [BorelSpace V] in
theorem klP_ne_zero : klP V ≠ 0 := by
  simp [klP]

omit [MeasurableSpace V] [BorelSpace V] in
theorem klP_ne_top : klP V ≠ ∞ := by
  simp [klP]

omit [MeasurableSpace V] [BorelSpace V] in
theorem klQ_ne_zero : klQ V ≠ 0 := by
  simp [klQ, klP]

omit [MeasurableSpace V] [BorelSpace V] in
theorem klQ_ne_top : klQ V ≠ ∞ := by
  unfold klQ
  exact ENNReal.div_ne_top (klP_ne_top (V := V)) (by norm_num)

/-- Real scaling factor `R^(-n/2)` on the local gradient/flux `L²` arm. -/
def klL2ScaleR (R : ℝ) : ℝ :=
  Real.rpow R (-klDim V / 2)

/-- `ENNReal` form of the local gradient/flux scale. -/
def klL2Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klL2ScaleR (V := V) R)

/-- Real scaling factor `R^(2/(n+4))` on the late gradient/flux
`L^(n+4)` arm. -/
def klLpScaleR (R : ℝ) : ℝ :=
  Real.rpow R (2 / (klDim V + 4))

/-- `ENNReal` form of the late gradient/flux scale. -/
def klLpScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klLpScaleR (V := V) R)

/-- Real scaling factor `R^(-n)` on the ordinary-source local `L¹` arm. -/
def klL1ScaleR (R : ℝ) : ℝ :=
  Real.rpow R (-klDim V)

/-- `ENNReal` form of the ordinary-source local scale. -/
def klL1Scale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klL1ScaleR (V := V) R)

/-- Real scaling factor `R^(4/(n+4))` on the ordinary-source late
`L^((n+4)/2)` arm. -/
def klLqScaleR (R : ℝ) : ℝ :=
  Real.rpow R (4 / (klDim V + 4))

/-- `ENNReal` form of the ordinary-source late scale. -/
def klLqScale (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (klLqScaleR (V := V) R)

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Exact Koch--Lamm solution control.  The value and gradient are explicit
data; a heat realization later proves that the second field is the spatial
derivative of the first. -/
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

/-- Exact Koch--Lamm ordinary source `Y⁰`: local `L¹` plus late
`L^((n+4)/2)`. -/
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

/-- Exact Koch--Lamm divergence source `Y¹`: local `L²` plus late
`L^(n+4)`. -/
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

/-- The split source class `f₀ + div f₁` consumed by the linear heat
potential.  The ordinary source and the divergence flux deliberately have
separate codomains: in the geometric applications `f₀` is `F`-valued while
`f₁` is an operator-valued field `V →L[ℝ] F`. -/
structure KLSplit (T : ℝ) (A₁ A_q A₂ Aₚ : ℝ≥0)
    (f₀ : ℝ × V → F) (f₁ : ℝ × V → G) : Prop where
  source : KLSource0 T A₁ A_q f₀
  flux : KLSource1 T A₂ Aₚ f₁

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
