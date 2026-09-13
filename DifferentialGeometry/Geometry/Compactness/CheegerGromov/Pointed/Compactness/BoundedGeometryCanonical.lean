import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.NormalCharts

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless] in
theorem eventually_curvDerivNorm_le_on_ball_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    ∀ A : Real, 0 < A → ∀ p : Nat, ∃ C : Real, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A →
          curvDerivNorm (I := I) p (X.obj i).metric x ≤ C := by
  intro A _hA p
  exact ⟨hgeom.C p, hgeom.nonneg p, Filter.Eventually.of_forall fun i => by
    intro _htop _hchart _hsmooth _ht2 _hsigma x _hx
    exact hgeom.bound i p x⟩

theorem exists_canonical_metric_compactness_of_boundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : Nat,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  classical
  let b := metricCompactSeedOfBoundedGeometry (I := I) X hcomplete hgeom hinj hconnected
  have hd : Nonempty (BoundedGeometryNormalChartData (I := I) X b.decay) :=
    nonempty_bounded_geometry_normal_chart_data (I := I) X hcomplete hconnected hgeom b.decay
      b.realizes
  let d := Classical.choice hd
  let C := b.higherRegularityCanonicalMetricCompactness d hcomplete hconnected
  have hconn :=
    b.higher_regularity_canonical_metric_compactness_connected d hcomplete hconnected
  exact ⟨C.compactness, C.domain_eq_canonical, C.reference_eq_limit, hconn⟩

end CheegerGromovCompactness
end DifferentialGeometry

end
