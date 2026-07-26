import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Euclidean split heat potentials

This file defines the full time-dependent heat potentials used by one
component of a Koch--Lamm split source.  An ordinary source is convolved with
the heat kernel, while one spatial component of a divergence source is
convolved with the corresponding first heat derivative.  The actual
divergence potential is the finite sum of the latter over an orthonormal
basis.

The CLM-valued fields `heatGrad0`, `heatGrad1`, and `heatSplitGrad` are the
exact spatial-gradient candidates.  The two integrand derivative theorems
below prove the pointwise calculus input needed to pass the derivative through
the spatial and time integrals.  The required Koch--Lamm domination estimates
remain a separate analytic layer.
-/

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

/-- Duhamel heat potential of an ordinary space-time source. -/
def heatPot0 (t : ℝ) (f : ℝ × V → F) (x : V) : F :=
  ∫ s in 0..t, ∫ y : V, heatKernel (t - s) (x - y) • f (s, y)

/-- Duhamel potential of one directional component of a divergence source. -/
def heatPot1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : F :=
  ∫ s in 0..t, ∫ y : V, heatD1 (t - s) w (x - y) • f (s, y)

/-- One componentwise split heat potential `f₀ + ∂_w f₁`. -/
def heatSplit (t : ℝ) (w : V) (f₀ f₁ : ℝ × V → F) (x : V) : F :=
  heatPot0 t f₀ x + heatPot1 t w f₁ x

/-- CLM-valued spatial-gradient candidate for the ordinary-source potential. -/
def heatGrad0 (t : ℝ) (f : ℝ × V → F) (x : V) : V →L[ℝ] F :=
  ∫ s in 0..t, ∫ y : V,
    (heatD1Map (t - s) (x - y)).smulRight (f (s, y))

/-- CLM-valued spatial-gradient candidate for one divergence-source
potential. -/
def heatGrad1 (t : ℝ) (w : V) (f : ℝ × V → F) (x : V) : V →L[ℝ] F :=
  ∫ s in 0..t, ∫ y : V,
    (heatD2Map (t - s) w (x - y)).smulRight (f (s, y))

/-- Spatial-gradient candidate for one componentwise split potential. -/
def heatSplitGrad (t : ℝ) (w : V) (f₀ f₁ : ℝ × V → F)
    (x : V) : V →L[ℝ] F :=
  heatGrad0 t f₀ x + heatGrad1 t w f₁ x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
/-- The ordinary-source spatial integrand has the first-heat-derivative CLM
as its exact Fréchet derivative. -/
theorem heatTerm0_fderiv {t s : ℝ} (hts : 0 < t - s)
    (f : ℝ × V → F) (x y : V) :
    HasFDerivAt (fun z : V ↦ heatKernel (t - s) (z - y) • f (s, y))
      ((heatD1Map (t - s) (x - y)).smulRight (f (s, y))) x := by
  simpa using
    ((heatKernel_hasFDeriv hts (x - y)).smul_const (f (s, y))).comp x
      ((hasFDerivAt_id x).sub_const y)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
/-- The directional-flux spatial integrand has the second-heat-derivative
CLM as its exact Fréchet derivative. -/
theorem heatTerm1_fderiv {t s : ℝ} (hts : 0 < t - s) (w : V)
    (f : ℝ × V → F) (x y : V) :
    HasFDerivAt (fun z : V ↦ heatD1 (t - s) w (z - y) • f (s, y))
      ((heatD2Map (t - s) w (x - y)).smulRight (f (s, y))) x := by
  simpa using
    ((heatD1_hasFDeriv hts w (x - y)).smul_const (f (s, y))).comp x
      ((hasFDerivAt_id x).sub_const y)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
