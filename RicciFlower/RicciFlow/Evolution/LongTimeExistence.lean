import RicciFlower.RicciFlow.Evolution.ScalarGradient

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Higher Derivative Estimates and Long-Time Existence

MSM110 Chapter 6.7 statement interfaces.

LaTeX labels covered here include `LongTimeExistSection`, `CurvatureBlowup`,
`Chapter5CurvatureDerivativeBoundsAssumed`,
`Chapter5CurvatureDerivativeBoundsUsed`, `MetricDerivativeBounds`,
`ContinuousLimitMetric`, `UniformEquivalenceOfMetrics`,
`OneTimeOneSpaceDerivative`, `BoundGamma`, `BoundDerivativesOfRicciInChart`,
`TermsToBoundForDGamma`, and `RicciDerivativeBounds`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

variable {M : Type*}

/-- The BBS estimate assumed from the derivative-estimates chapter. -/
def BBSDerivativeEstimateOn
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real) : Prop :=
  ∀ (alpha K : Real) (m : Nat),
    0 < alpha -> 0 < K ->
      (∀ t x, 0 ≤ t -> t ≤ alpha / K -> curvNorm t x ≤ K) ->
        ∃ C : Real, ∀ t x, 0 < t -> t ≤ alpha / K ->
          derivNorm m t x ≤ C * K / t ^ m

/-- Consequence of BBS estimates under a uniform curvature bound on `[0,T]`. -/
def UniformCurvatureDerivativeBoundsOn
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real)
    (K T : Real) : Prop :=
  ∀ m : Nat, ∃ C : Real, ∀ t x,
    0 ≤ t -> t ≤ T -> curvNorm t x ≤ K -> derivNorm m t x ≤ C

/-- Bounds on background-coordinate derivatives of the evolving metric. -/
def MetricDerivativeBoundsOn
    (metricDerivNorm : Nat -> Real -> M -> Real) (T : Real) : Prop :=
  ∀ m : Nat, ∃ C : Real, ∀ t x, 0 ≤ t -> t < T ->
    metricDerivNorm m t x ≤ C

/-- Continuous terminal metric and uniform equivalence produced from an
integrable metric time derivative. -/
def ContinuousLimitMetricAt
    (metricDistToLimit : Real -> M -> Real) (T : Real) : Prop :=
  ∀ eps : Real, 0 < eps -> ∃ tau : Real, tau < T ∧
    ∀ t x, tau ≤ t -> t < T -> metricDistToLimit t x ≤ eps

/-- Uniform equivalence of metrics under bounded Ricci/time derivative. -/
def UniformEquivalenceOfMetricsOn
    (metricRatioUpper metricRatioLower : Real -> M -> Real)
    (lowerBound upperBound T : Real) : Prop :=
  ∀ t x, 0 ≤ t -> t ≤ T ->
    metricRatioUpper t x ≤ upperBound ∧ lowerBound ≤ metricRatioLower t x

/-- Bounds on background derivatives of Ricci. -/
def RicciDerivativeBoundsOn
    (ricciDerivNorm : Nat -> Real -> M -> Real) (T : Real) : Prop :=
  ∀ m : Nat, ∃ C : Real, ∀ t x, 0 ≤ t -> t < T ->
    ricciDerivNorm m t x ≤ C

/-- Display `OneTimeOneSpaceDerivative`, a mixed time/space derivative bound
for metric components in one background chart. -/
def OneTimeOneSpaceDerivativeEstimateOn
    (mixedMetricDerivNorm : Real -> M -> Real) (T C : Real) : Prop :=
  ∀ (t : Real) (x : M), 0 ≤ t -> t < T -> mixedMetricDerivNorm t x ≤ C

/-- Display `BoundGamma`, the local Christoffel-coordinate bound used in the
long-time existence chart argument. -/
def ChristoffelCoordBoundOn
    (gammaNorm : Real -> M -> Real) (T C : Real) : Prop :=
  ∀ (t : Real) (x : M), 0 ≤ t -> t < T -> gammaNorm t x ≤ C

/-- Display `BoundDerivativesOfRicciInChart`, bounds on coordinate derivatives
of Ricci in a fixed chart. -/
def RicciChartDerivativeBoundsOn
    (ricciChartDerivNorm : Nat -> Real -> M -> Real) (T : Real) : Prop :=
  ∀ m : Nat, ∃ C : Real, ∀ t x, 0 ≤ t -> t < T ->
    ricciChartDerivNorm m t x ≤ C

/-- Display `TermsToBoundForDGamma`, the collection of product-rule terms that
must be bounded to control `d Gamma`. -/
def DGammaTermsToBoundOn
    (termNorm : Nat -> Real -> M -> Real) (T : Real) : Prop :=
  ∀ m : Nat, ∃ C : Real, ∀ t x, 0 ≤ t -> t < T -> termNorm m t x ≤ C

/-- Maximal finite-time curvature blowup conclusion. -/
def CurvatureBlowupAtMaximalTime
    (curvSup : Real -> Real) (T : Real) : Prop :=
  0 < T ∧ ∀ K : Real, ∃ t : Real, t < T ∧ K < curvSup t

theorem chapter_five_curvature_derivative_bounds_assumed
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real) :
    BBSDerivativeEstimateOn curvNorm derivNorm := by
  sorry

theorem chapter_five_curvature_derivative_bounds_used
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (_hBBS : BBSDerivativeEstimateOn curvNorm derivNorm)
    (_hcurv : ∀ t x, 0 ≤ t -> t ≤ T -> curvNorm t x ≤ K) :
    UniformCurvatureDerivativeBoundsOn curvNorm derivNorm K T := by
  sorry

theorem metric_derivative_bounds
    (metricDerivNorm curvNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (_hcurv : ∀ t x, 0 ≤ t -> t < T -> curvNorm 0 t x ≤ K) :
    MetricDerivativeBoundsOn metricDerivNorm T := by
  sorry

theorem continuous_limit_metric
    (metricDistToLimit : Real -> M -> Real) (T C : Real)
    (_hintegrableTimeDerivative : Prop) :
    ContinuousLimitMetricAt metricDistToLimit T := by
  sorry

theorem uniform_equivalence_of_metrics
    (metricRatioUpper metricRatioLower : Real -> M -> Real) (K T : Real)
    (_hricciBound : Prop) :
    ∃ lowerBound upperBound : Real,
      UniformEquivalenceOfMetricsOn
        metricRatioUpper metricRatioLower lowerBound upperBound T := by
  sorry

theorem ricci_derivative_bounds
    (ricciDerivNorm curvNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (_hcurv : ∀ t x, 0 ≤ t -> t < T -> curvNorm 0 t x ≤ K) :
    RicciDerivativeBoundsOn ricciDerivNorm T := by
  sorry

theorem curvature_blowup
    (curvSup : Real -> Real) (T : Real)
    (_hmaximal : Prop)
    (_hshortTimeExistence : Prop)
    (_hBBS : Prop) :
    CurvatureBlowupAtMaximalTime curvSup T := by
  sorry

end RicciFlow
end RicciFlower
