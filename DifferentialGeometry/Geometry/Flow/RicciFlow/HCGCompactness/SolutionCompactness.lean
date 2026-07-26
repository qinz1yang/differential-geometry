import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitUpgrade

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Flow Solution Compactness

The canonical MSM135 Theorem 3.10 consumer in this file takes a concrete
Theorem 3.9 conclusion together with `FlowUpgradeData`.  In particular, this
module does not expose a backend that accepts the desired compactness conclusion
as an input.
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

/-- MSM135 Theorem 3.10 from a concrete time-zero metric compactness conclusion
and the exposed P4 smooth-flow-limit data. -/
theorem solutionComp_of_mc
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (hflow : FlowUpgradeData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  hflow.toConclusion

end HCGCompactness
end DifferentialGeometry
