import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitUpgrade

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem solutionComp_of_mc
    [FiniteDimensional Real E]
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (hflow : FlowUpgradeData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  hflow.toConclusion

end HCGCompactness
end DifferentialGeometry
