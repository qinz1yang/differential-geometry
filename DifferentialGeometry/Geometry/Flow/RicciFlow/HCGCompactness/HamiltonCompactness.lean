import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.SolutionCompactnessInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Compactness Theorem Interface

This is the RicciFlower-native theorem shape corresponding to MSM135 Chapter 3,
Theorem "Compactness for solutions".  The checked endpoint is deliberately
conditional on the concrete metric-compactness and flow-upgrade producers.
-/

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

/-- Canonical conditional Hamilton compactness consumer.  It follows the
checked Chapter 4 Theorem 3.9 endpoint with concrete `FlowUpgradeData`; no
unconditional compactness theorem or exact-conclusion backend is invoked. -/
theorem compactnessSol_cond
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (inp : MetricCompactnessInputs (I := I) (X.atZero (I := I)))
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hflowInj : FlowBaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : FlowUpgradeData (I := I) X
      (MetricCompactnessInputs.metricCompactness (I := I)
        inp hcomplete0 hderiv.at_zero_geom hflowInj hconn)) :
    CompactnessConclusion (I := I) X :=
  solutionComp_cond (I := I) X inp hcomplete0 hflowInj hconn hderiv hflow

/-- **MSM135 Theorem 3.10 (Compactness for solutions).**  A sequence of
complete pointed Ricci flows on one open interval, with locally uniform
curvature bounds and a uniform time-zero basepoint injectivity-radius bound,
has a smoothly convergent pointed subsequence on that open interval. -/
theorem compactnessSol
    {α b : Real} (h0 : (0 : Real) ∈ Set.Ioo α b)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.openInterval
        α b 0 h0)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X)
    (hinj : FlowBaseInjBound (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      ConnectedSpace (X.term k).M) :
    ∃ L : PointedFlowData.{u, uE, uH} (I := I) X.D,
      ∃ subseq : Nat → Nat,
        StrictMono subseq ∧
          Nonempty (SmoothCGHConverges (I := I) X L subseq) ∧
            ∀ t : Real, t ∈ X.D.carrier →
              MetricComplete (I := I) (L.atTime (I := I) t) := by
  have hzero : (0 : Real) ∈ X.D.carrier := by
    rw [hD]
    exact h0
  have hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)) :=
    hcomplete.at_time hzero
  sorry

end HCGCompactness
end DifferentialGeometry
