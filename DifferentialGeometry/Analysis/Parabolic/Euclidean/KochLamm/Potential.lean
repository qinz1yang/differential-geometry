import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Lp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatPot0 (t : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ s in 0..t, ∫ y : V, heatKernel (t - s) (x - y) • f (s, y)

def heatPot1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ s in 0..t, ∫ y : V, heatD1 (t - s) w (x - y) • f (s, y)

def heatSplit (t : ℝ) (w : V) (f₀ f₁ : ℝ × V → F) (x : V) : F :=
  heatPot0 t f₀ x + heatPot1 t w f₁ x

def heatGrad0 (t : ℝ) (f : ℝ × V → F) (x : V) : V →L[ℝ] F :=
  ∫ s in 0..t, ∫ y : V,
    (heatD1Map (t - s) (x - y)).smulRight (f (s, y))

def heatGrad1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : V →L[ℝ] F :=
  ∫ s in 0..t, ∫ y : V,
    (heatD2Map (t - s) w (x - y)).smulRight (f (s, y))

def heatSplitGrad (t : ℝ) (w : V) (f₀ f₁ : ℝ × V → F)
    (x : V) : V →L[ℝ] F :=
  heatGrad0 t f₀ x + heatGrad1 t w f₁ x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
theorem heatTerm0_fderiv {t s : ℝ} (f : ℝ × V → F) (x y : V) :
    HasFDerivAt (fun z : V ↦ heatKernel (t - s) (z - y) • f (s, y))
      ((heatD1Map (t - s) (x - y)).smulRight (f (s, y))) x := by
  change HasFDerivAt
    ((fun z => heatKernel (t - s) z • f (s, y)) ∘ fun z : V => z - y)
      ((heatD1Map (t - s) (x - y)).smulRight (f (s, y))) x
  exact ((heatKernel_hasFDeriv (x - y)).smul_const (f (s, y))).comp x
    ((hasFDerivAt_id x).sub_const y)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
theorem heatTerm1_fderiv {t s : ℝ} (w : V) (f : ℝ × V → F) (x y : V) :
    HasFDerivAt (fun z : V ↦ heatD1 (t - s) w (z - y) • f (s, y))
      ((heatD2Map (t - s) w (x - y)).smulRight (f (s, y))) x := by
  change HasFDerivAt
    ((fun z => heatD1 (t - s) w z • f (s, y)) ∘ fun z : V => z - y)
      ((heatD2Map (t - s) w (x - y)).smulRight (f (s, y))) x
  exact ((heatD1_hasFDeriv w (x - y)).smul_const (f (s, y))).comp x
    ((hasFDerivAt_id x).sub_const y)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
