import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

theorem metricCompactness_reference_eq_limit
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := inp.metricCompactness hcomplete hconn
    ∀ k : ℕ, (C.convergence.metrics.domain k).referenceMetric =
      (C.convergence.metrics.domain k).limitMetric := by
  exact fun k => (inp.canonicalMetricCompactness hcomplete hconn).reference_eq_limit k

theorem metricCompactness_limit_connected
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := inp.metricCompactness hcomplete hconn
    let _ : TopologicalSpace C.limit.M := C.limit.topology
    ConnectedSpace C.limit.M := by
  classical
  dsimp only [MetricCompactnessAssumptions.metricCompactness,
    MetricCompactnessAssumptions.canonicalMetricCompactness,
    CanonicalMetricCompactness.ofSubsequence, MetricCompactLimit.ofSeqSubseq]
  exact canonical_metric_compactness_connected (I := I) _ _

theorem exists_metricCompactness_full_ambient_quadratic_control
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := inp.metricCompactness hcomplete hconn
    let _ : TopologicalSpace C.limit.M := C.limit.topology
    let _ : ChartedSpace H C.limit.M := C.limit.charted
    let _ : IsManifold I ∞ C.limit.M := C.limit.smooth
    ∀ K : Set C.limit.M, IsCompact K → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → K ⊆ C.maps.source k ∧
        (let _ : TopologicalSpace (X.obj (C.subseq k)).M :=
           (X.obj (C.subseq k)).topology
         let _ : ChartedSpace H (X.obj (C.subseq k)).M :=
           (X.obj (C.subseq k)).charted
         let _ : IsManifold I ∞ (X.obj (C.subseq k)).M :=
           (X.obj (C.subseq k)).smooth
         ∀ x : C.limit.M, x ∈ K → ∀ v : TangentSpace I x,
           |(X.obj (C.subseq k)).metric.inner (C.maps.map k x)
               (mfderiv I I (C.maps.map k) x v) (mfderiv I I (C.maps.map k) x v) -
             C.limit.metric.inner x v v| ≤ epsilon * C.limit.metric.inner x v v) := by
  let C := inp.metricCompactness hcomplete hconn
  let _ : TopologicalSpace C.limit.M := C.limit.topology
  let _ : ChartedSpace H C.limit.M := C.limit.charted
  let _ : IsManifold I ∞ C.limit.M := C.limit.smooth
  dsimp only
  intro K hK epsilon hepsilon
  exact exists_pointed_full_ambient_quadratic_control C.convergence.metrics
    (metricCompactness_reference_eq_limit inp hcomplete hconn)
    K hK epsilon hepsilon

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
