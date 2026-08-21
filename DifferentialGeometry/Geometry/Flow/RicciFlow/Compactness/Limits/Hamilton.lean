import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Solution

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.SolutionInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.BoundedGeometryCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.CanonicalCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local

open DifferentialGeometry.Geometry.Curvature

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

theorem compactnessSol_cond
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
    CompactnessConclusion (I := I) X :=
  solutionComp_cond (I := I) X inp hcomplete0 hconn hflow

theorem compactnessSol
    {α b : Real} (h0 : (0 : Real) ∈ Set.Ioo α b)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval
        α b 0 h0)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X)
    (hinj : FlowerScaleInjBound (I := I) X)
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
  let hgeom0 : SeqBoundedGeometry (I := I) (X.atZero (I := I)) :=
    CurvBoundInput.atZeroGeomOpen (I := I) h0 X hD hcomplete hcurv
  have hconn0 : ∀ k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    simpa [PointedFlowSeq.atZero] using hconn k
  let seed : MetricCompactSeed (I := I) (X.atZero (I := I)) :=
    metricSeedOfBG (I := I) (X.atZero (I := I))
      hcomplete0 hgeom0 hinj hconn0
  have hd : Nonempty (BoundedGeometryNormalData (I := I) (X.atZero (I := I)) seed.decay) :=
    exists_bounded_geometry_normal_data (I := I) (X.atZero (I := I))
      hcomplete0 hconn0 hgeom0 seed.decay seed.realizes
  let canon : CanonicalMetricCompactness (I := I) (X.atZero (I := I)) :=
    seed.higherRegularityCanonicalMetricCompactness (Classical.choice hd) hcomplete0 hconn0
  obtain ⟨d, hcompleteL⟩ :=
    open_upgrade_of_canonical_metric_compactness (I := I) canon h0 hD hcomplete hcurv
  let mc' : MetricCompactnessConclusion (I := I) (X.atZero (I := I)) :=
    canon.compactness.compSubseq d.φ d.hφ
  refine ⟨d.data.L, mc'.subseq, mc'.strictMono, ?_, hcompleteL⟩
  exact ⟨SmoothCGHConverges.ofRestrictPullback (I := I)
    d.data.maps d.data.scalar d.data.ricciNorm d.data.hσsrc
    d.data.refMetric
    (letI : TopologicalSpace d.data.L.M := d.data.L.topology
     letI : ChartedSpace H d.data.L.M := d.data.L.charted
     letI : IsManifold I ∞ d.data.L.M := d.data.L.smooth
     letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) d.data.L.M := by
       change IsManifold I ∞ d.data.L.M
       infer_instance
     letI : SigmaCompactSpace d.data.L.M := d.data.L.sigmaCompact
     letI : T2Space d.data.L.M := d.data.L.t2
     d.data.L.S.family.metric) d.data.conv⟩

end HCGCompactness
end DifferentialGeometry
