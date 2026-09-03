import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Solution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.InjectivityRadius

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

omit [Module.Finite ℝ E] in
theorem solutionComp_cond
    [Module.Finite ℝ E]
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (inp : MetricCompactnessInputs (I := I) (X.atZero (I := I)))
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M)
    (hflow : FlowUpgrade (I := I) X
      (MetricCompactnessInputs.metricCompactness (I := I)
        inp hcomplete0 hconn)) :
    compactnessConclusion (I := I) X :=
  solutionComp_of_mc (I := I) X
    (MetricCompactnessInputs.metricCompactness (I := I)
      inp hcomplete0 hconn)
    hflow

end HCGCompactness
end DifferentialGeometry
