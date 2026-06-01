import DifferentialGeometry.Realized.LeviCivita.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# DifferentialGeometry Realized Ricci-Flow Interfaces

The Ricci-flow equation is a predicate on a realized metric family. It is not a
field of a solution record.
-/

namespace DifferentialGeometry
namespace Realized

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- A Ricci tensor field supplied to the Ricci-flow equation.

The general curvature layer uses its own pointwise tensor aliases; this file
does not import that layer, so Ricci flow does not sit below general curvature. -/
abbrev RicciTensorField (Time : Type*) :=
  Time -> (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

/-- The Ricci-flow metric variation equation, evaluated on fixed tangent vectors.

This is the realized version of `partial_t g = -2 Ric`. -/
def MetricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time) : Prop :=
  forall (t : Time) (x : M) (X Y : TangentSpace I x),
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y

/-- The metric evolution theorem extracted from the equation predicate. -/
theorem metric_dt_eq_neg_two_ricci_of_metricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time)
    (hEq : MetricVariationEquation td G Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y :=
  hEq t x X Y

/-- A data-only realized Ricci-flow candidate.

Being a Ricci-flow solution is expressed by `IsRealizedRicciFlow`, not by a
proof field on this structure. -/
structure RealizedRicciFlowData where
  family : RealizedMetricFamily (I := I) (M := M) Time

/-- Predicate saying that a data-only realized family solves the Ricci-flow equation
for the supplied Ricci tensor field. -/
def IsRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RicciTensorField (I := I) (M := M) Time) : Prop :=
  MetricVariationEquation td S.family Ric

theorem metric_dt_eq_neg_two_ricci_of_isRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RicciTensorField (I := I) (M := M) Time)
    (hS : IsRealizedRicciFlow td S Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td S.family t x X Y = (-2 : Real) * Ric t x X Y :=
  metric_dt_eq_neg_two_ricci_of_metricVariationEquation td S.family Ric hS t x X Y

section Interval

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

/-- The Ricci-flow metric variation equation on a concrete real time interval.

It is stated with `HasDerivWithinAt` on the interval carrier, and only required
at regular times. -/
def MetricVariationEquationOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real) : Prop :=
  forall (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x),
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real)

/-- A data-only realized Ricci-flow candidate on a real interval. -/
structure RealizedRicciFlowCandidateOn (D : RealTimeInterval) where
  family : RealizedMetricFamilyOn (I := I) (M := M) D
  ricci : RicciTensorField (I := I) (M := M) Real

/-- Predicate package saying a data-only interval family is a Ricci-flow
solution. Curvature realization is available in the curvature layer below this
file; this package starts from an explicit Ricci tensor field. -/
structure IsRealizedRicciFlowSolutionOn
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D) : Prop where
  smoothMetric : MetricFamilySmoothOn (I := I) (M := M) D S.family
  smoothConnection : ConnectionFamilySmoothOn (I := I) (M := M) S.family
  leviCivita : LeviCivita.IsLeviCivitaFamilyOn (I := I) S.family
  equation : MetricVariationEquationOn (I := I) S.family S.ricci

/-- The interval metric-evolution theorem extracted from the equation
predicate. -/
theorem metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (hEq : MetricVariationEquationOn (I := I) G Ric)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hEq t x X Y

/-- The interval metric-evolution theorem extracted from a Ricci-flow solution
package. -/
theorem metric_derivWithin_eq_neg_two_ricci_of_isRealizedRicciFlowSolutionOn
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricci (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hS.equation t x X Y

end Interval

end Realized
end DifferentialGeometry
