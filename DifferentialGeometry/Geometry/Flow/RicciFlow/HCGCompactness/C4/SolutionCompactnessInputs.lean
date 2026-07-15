import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionCompactness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Conditional MSM135 Theorem 3.10

This module is the honest Chapter 4 to Chapter 3 handoff.  It first invokes the
conditional Theorem 3.9 endpoint and then consumes concrete `FlowUpgradeData`.
It does not call the unconditional `metricCompactness` frontier or the legacy
exact-conclusion field `SmoothFlowLimitInput.upgrade`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- **MSM135 Theorem 3.10, conditional form.**  Apply the conditional
Theorem 3.9 endpoint at time zero, then assemble the concrete P4 upgrade data
over the resulting metric compactness conclusion. -/
theorem solutionComp_cond
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (inp : MetricCompactnessInputs (I := I) (X.atZero (I := I)))
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hinj : FlowBaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : FlowUpgradeData (I := I) X
      (MetricCompactnessInputs.metricCompactness (I := I)
        inp hcomplete0 hderiv.at_zero_geom hinj hconn)) :
    CompactnessConclusion (I := I) X :=
  solutionComp_of_mc (I := I) X
    (MetricCompactnessInputs.metricCompactness (I := I)
      inp hcomplete0 hderiv.at_zero_geom hinj hconn)
    hflow

end HCGCompactness
end DifferentialGeometry
